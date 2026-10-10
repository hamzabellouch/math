import OAI.Combinatorics.Progressions.Sampling.AllocatedGridlessProfileBound

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedGridJetScale_le_uniform :
    let K : ℝ := (S.value : ℝ) ^ (layerTailDegree m + 1)
    let D := Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    allocatedGridJetScale B U b S (O := O) ≤
      (K ^ D) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} := by
  intro K D
  have hK : 1 ≤ K := one_le_pow₀ (by exact_mod_cast S.positive)
  unfold allocatedGridJetScale
  rw [← Finset.card_univ (α := {a // allocatedGridAxis (I := I) U b S.value a}),
    ← Finset.prod_const]
  apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
  intro a _
  have ha : (allocatedGridAxisScale B U b S a : ℝ) ≤ K := by
    dsimp only [K]
    exact_mod_cast (allocatedGridAxisScale_bounds B U b S a).2
  have hd : Fintype.card (O a.val.1) ≤ D := by
    apply Fintype.card_le_of_injective (fun t : O a.val.1 => (⟨a.val, t⟩ : Σ c : LayerSamplerAxis I n, O c.1))
    intro t w h
    exact eq_of_heq (Sigma.mk.inj h).2
  exact (pow_le_pow_left₀ (by positivity) ha _).trans (pow_le_pow_right₀ hK hd)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "rows" => (fun j => (Subtype.val : jets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "invVolume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))⁻¹
local notation "longScale" => (∏ a, allocatedLongJetOutputScale B U b S (O := jets) a)

noncomputable def allocatedGridlessEnvelopeCap (A : ℝ≥0) (V : Fin m → ℝ≥0) : ℝ≥0 :=
  allocatedProfileErrorCap B U b S (O := jets) A ‖invVolume‖₊ 0 V

theorem allocatedIdealSiteEnvelope_le_invVolume (hR : ∀ j, 0 < R j)
    (z : AllocatedLongJetRows B U b S jets) :
    allocatedIdealSiteEnvelope B U b S z ≤ invVolume := by
  unfold allocatedIdealSiteEnvelope
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.mpr (Finset.prod_nonneg (fun q _ => (hR q.1.val.1).le))

variable (hR : ∀ j, 0 < R j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

include hR in
theorem allocatedGridlessSiteEnvelope_abs_le (modulus : ℕ)
    (residue : ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (A : ℝ≥0)
    (hA : ∀ (z : AllocatedLongJetRows B U b S jets) (r : ∀ j, jets j → Q j → ZMod d),
      |∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)| *
      coefficientDeckJetDensity root dirs rows d r ≤ A)
    (V : Fin m → ℝ≥0)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (y : EuclideanJetLayers U jets) :
    |allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d
      (allocatedMaskedSiteEnvelope B U b S x modulus residue) y| ≤
      allocatedGridlessEnvelopeCap (α := α) B U b S A V := by
  have hi : 0 ≤ invVolume := inv_nonneg.mpr (Finset.prod_nonneg (fun q _ => (hR q.1.val.1).le))
  have hl : 0 < longScale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  have hn : (‖invVolume‖₊ : ℝ) = invVolume := by
    change ‖invVolume‖ = invVolume
    exact Real.norm_of_nonneg hi
  have he := allocatedGridlessCoveredProfile_abs_le B U b S x u v rows hb o bW d
    (allocatedMaskedSiteEnvelope B U b S x modulus residue) (mul_nonneg A.coe_nonneg hi) (fun z r => by
      rw [allocatedMaskedSiteEnvelope, abs_div, abs_mul,
        abs_of_nonneg (allocatedIdealSiteEnvelope_nonneg B U b S hR z), abs_of_pos hl]
      calc
        _ = ((|∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)| *
            coefficientDeckJetDensity root dirs rows d r) * allocatedIdealSiteEnvelope B U b S z) / longScale := by ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul (hA z r) (allocatedIdealSiteEnvelope_le_invVolume B U b S hR z)
            (allocatedIdealSiteEnvelope_nonneg B U b S hR z) A.coe_nonneg) hl.le) y
  apply he.trans
  simp only [allocatedGridlessEnvelopeCap, allocatedProfileErrorCap, allocatedErrorKernelCap,
    add_zero, one_mul, NNReal.coe_mul, NNReal.coe_prod, NNReal.coe_pow, NNReal.coe_natCast, hn]
  calc
    _ ≤ (A * invVolume) *
        (((S.value : ℝ) ^ (layerTailDegree m + 1)) ^ Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)) ^
          Fintype.card {a // grid a} * (∏ j, (V j : ℝ) ^ Fintype.card (jets j)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (allocatedGridJetScale_le_uniform B U b S (O := jets))
          (mul_nonneg A.coe_nonneg hi)
      · exact Finset.prod_le_prod₀ (fun j _ => pow_nonneg (hV j).1 _)
          (fun j _ => pow_le_pow_left₀ (hV j).1 (hV j).2 _)
      · exact Finset.prod_nonneg (fun j _ => pow_nonneg (hV j).1 _)
      · exact mul_nonneg (mul_nonneg A.coe_nonneg hi) (by positivity)
    _ = _ := by ring

include hR in
omit [DecidableEq α]
  [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedGridlessEnvelopeCap_le_exp {P : ℝ} (hP : 0 ≤ P)
    (hm : (m : ℝ) ≤ P) (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ P)
    (hout : (Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1) : ℝ) ≤ P)
    (hrows : ∀ j, (Fintype.card (jets j) : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp P)
    (V : Fin m → ℝ≥0) (hV : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hK : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) :
    (allocatedGridlessEnvelopeCap (α := α) B U b S A V : ℝ) ≤
      Real.exp (allocatedErrorKernelLog P + P ^ 2) := by
  have hcap := (allocatedErrorKernel_exp_bounds B U b S (O := jets) 1 A (fun _ => 0) V
    hP hm haxes hout hrows hJ le_rfl hA hK (fun _ => (Real.exp_pos _).le) hV).1
  have hcount : (Fintype.card output : ℝ) ≤ P :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective
      (fun q : output => (⟨q.1.val, q.2⟩ : Σ a : LayerSamplerAxis I n, jets a.1))
      (by
        rintro ⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb⟩, y⟩ h
        have hab : a = b := (Sigma.mk.inj h).1
        cases hab
        have hxy : x = y := eq_of_heq (Sigma.mk.inj h).2
        cases hxy
        rfl))).trans hout
  have hvol := allocatedSiteBuffer_cap_le_exp (α := α) B U b S hP hcount (fun j => (hR j).le) hRi
  simp only [allocatedGridlessEnvelopeCap, allocatedProfileErrorCap, add_zero, NNReal.coe_mul]
  calc
    _ ≤ Real.exp (allocatedErrorKernelLog P) * Real.exp (P ^ 2) :=
      mul_le_mul hcap (by simpa only [pow_two] using hvol) (NNReal.coe_nonneg _) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

end Erdos3.VectorPolynomial

end

end OAI
