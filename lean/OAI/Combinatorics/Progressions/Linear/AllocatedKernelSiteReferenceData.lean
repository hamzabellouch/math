import OAI.Combinatorics.Progressions.Estimates.CanonicalSiteBlocks
import OAI.Combinatorics.Progressions.Lattices.AllocatedIdealResidueData

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedKernelSiteParameter {A : Type*} [Semiring A]
    (p Ebad T : A) : A := allocatedKernelPrimitiveBudget p Ebad T + p ^ 2

theorem allocatedKernelSiteParameter_bounds {p Ebad T : ℝ}
    (hp : 0 ≤ p) (hEbad : 0 ≤ Ebad) (hT : 0 ≤ T) :
    let Q := allocatedKernelSiteParameter p Ebad T
    0 ≤ Q ∧ p ≤ Q ∧ allocatedKernelPrimitiveBudget p Ebad T ≤ Q ∧ p ^ 2 ≤ Q := by
  have h := allocatedKernelPrimitiveBudget_bounds hp hEbad hT
  dsimp only [allocatedKernelSiteParameter]
  have hs := sq_nonneg p
  exact ⟨by linarith [h.1], by linarith [h.2.1], by linarith, by linarith [h.1]⟩

theorem allocatedKernelSiteParameter_mono {p Ebad T p' Ebad' T' : ℝ}
    (hp : 0 ≤ p) (hEbad : 0 ≤ Ebad) (hT : 0 ≤ T)
    (hpp : p ≤ p') (hEE : Ebad ≤ Ebad') (hTT : T ≤ T') :
    allocatedKernelSiteParameter p Ebad T ≤ allocatedKernelSiteParameter p' Ebad' T' :=
  add_le_add (allocatedKernelPrimitiveBudget_mono hp hEbad hT hpp hEE hTT)
    (pow_le_pow_left₀ hp hpp 2)

theorem allocatedKernelSiteParameter_refined_budget (m : ℕ) {dim : ℕ}
    (hdim : dim ≤ m + 1) {p Ebad T : ℝ}
    (hp : 0 ≤ p) (hEbad : 0 ≤ Ebad) (hT : 0 ≤ T) :
    (m + 1 : ℕ) * allocatedKernelPrimitiveBudget p Ebad T + p ^ 2 + (dim + 1 : ℕ) ≤
      allocatedSiteScaleNumeric m (allocatedKernelSiteParameter p Ebad T) := by
  have hQ := (allocatedKernelSiteParameter_bounds hp hEbad hT).1
  have hnum := (allocatedSiteScaleNumeric_bounds m hQ).2.2
  have hd : ((dim + 1 : ℕ) : ℝ) ≤ (m + 2 : ℕ) := by exact_mod_cast (show dim + 1 ≤ m + 2 by omega)
  have hm : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast (show 1 ≤ m + 1 by omega)
  have hs := mul_le_mul_of_nonneg_right hm (sq_nonneg p)
  dsimp only [allocatedKernelSiteParameter] at hnum ⊢
  nlinarith

theorem allocatedSiteSourceLog_mono (m : ℕ) {p e E p' e' E' : ℝ}
    (hp : 0 ≤ p) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hpp : p ≤ p') (hee : e ≤ e') (hEE : E ≤ E') :
    allocatedSiteSourceLog m p e E ≤ allocatedSiteSourceLog m p' e' E' := by
  have hD : allocatedComparisonDimension m p ≤ allocatedComparisonDimension m p' := by
    unfold allocatedComparisonDimension
    gcongr
  have hN : allocatedSiteScaleNumeric m p ≤ allocatedSiteScaleNumeric m p' := by
    unfold allocatedSiteScaleNumeric
    gcongr
  have hw : allocatedSiteKernelMaskLog m p ≤ allocatedSiteKernelMaskLog m p' := by
    unfold allocatedSiteKernelMaskLog
    gcongr
  have hC : canonicalScalarSourceLog m p ≤ canonicalScalarSourceLog m p' := by
    unfold canonicalScalarSourceLog
    gcongr
  have hL := allocatedIdealScaleLog_mono m (allocatedComparisonDimension_bounds m hp).1
    (allocatedSiteScaleNumeric_bounds m hp).1 he (allocatedSiteKernelMaskLog_nonneg m hp) hE
    hD hN hee hw hEE
  change allocatedSiteScaleLog m p e E ≤ allocatedSiteScaleLog m p' e' E' at hL
  unfold allocatedSiteSourceLog
  linarith

theorem exists_allocatedKernelSiteSourceLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p Ebad T e E : ℝ},
      0 ≤ p → 0 ≤ Ebad → 0 ≤ T → 0 ≤ e → 0 ≤ E →
      allocatedSiteSourceLog m (allocatedKernelSiteParameter p Ebad T) e E ≤
        (p + Ebad + T + e + E + a) ^ a := by
  let poly : Polynomial ℕ := allocatedSiteSourceLog m
    (allocatedKernelSiteParameter Polynomial.X Polynomial.X Polynomial.X) Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p Ebad T e E hp hEbad hT he hE
  have hQ := allocatedKernelSiteParameter_mono hp hEbad hT
    (show p ≤ p + Ebad + T + e + E by linarith)
    (show Ebad ≤ p + Ebad + T + e + E by linarith)
    (show T ≤ p + Ebad + T + e + E by linarith)
  apply (allocatedSiteSourceLog_mono m (allocatedKernelSiteParameter_bounds hp hEbad hT).1
    he hE hQ (show e ≤ p + Ebad + T + e + E by linarith)
      (show E ≤ p + Ebad + T + e + E by linarith)).trans
  simpa [poly, allocatedKernelSiteParameter, allocatedKernelPrimitiveBudget,
    allocatedSiteSourceLog, allocatedSiteScaleLog, allocatedSiteScaleNumeric,
    allocatedSiteKernelMaskLog, canonicalScalarSourceLog, allocatedComparisonDimension,
    allocatedIdealScaleLog, allocatedIdealScaleInput, allocatedPhysicalIdealLengthEnvelope,
    allocatedTestLengthEnvelope, allocatedJointLengthEnvelope, allocatedTestEnvelope,
    allocatedFrontEnvelope, allocatedAccuracyEnvelope, allocatedTupleEnvelope,
    allocatedKernelEnvelope, allocatedIdealMeshEnvelope, allocatedIdealGridEnvelope,
    allocatedIdealRadiusEnvelope, allocatedProxyLipEnvelope, allocatedIdealLipEnvelope,
    allocatedSupportEnvelope, allocatedDensityEnvelope, kernelOutputEnvelope,
    kernelGeometryEnvelope, kernelInverseEnvelope, Polynomial.eval₂_pow] using
      hbound (p + Ebad + T + e + E) (by positivity)

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

noncomputable def allocatedKernelSiteScale (p Ebad T e E : ℝ) : LayerSamplerScale (G := G) B U b R σ :=
  allocatedSiteScale B U b hR hσ (allocatedKernelSiteParameter p Ebad T) e E

theorem allocatedKernelSiteScale_cutoff {dim : ℕ} [Nonempty (Fin dim)] {p Ebad T e E : ℝ}
    (hp : 0 ≤ p) (hEbad : 0 ≤ Ebad) (hT : 0 ≤ T) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdim : (dim : ℝ) ≤ p) (hG : (Fintype.card G : ℝ) ≤ p)
    {M D : ℕ} (hM : 0 < M) (hD : 0 < D)
    (hMT : (M : ℝ) ≤ Real.exp T) (hDp : (D : ℝ) ≤ Real.exp p) :
    let cutoff := scalarKernelCutoff (Fin dim) G M D (Real.exp (-(Ebad + 1)))
    0 < cutoff ∧ (cutoff : ℝ) ≤ Real.exp (allocatedKernelPrimitiveBudget p Ebad T) ∧
      cutoff ≤ (allocatedKernelSiteScale (G := G) B U b hR hσ p Ebad T e E).value := by
  have hQ := allocatedKernelSiteParameter_bounds hp hEbad hT
  have hcut := scalarKernelCutoff_le_allocatedPrimitive (Fin dim) G hp hEbad hT
    (by simpa only [Fintype.card_fin] using hdim) hG hM hD hMT hDp
  refine ⟨(scalarKernelCutoff_bounds (Fin dim) G hM hD (Real.exp_pos _)).1, hcut, ?_⟩
  have hnum := (allocatedSiteScaleNumeric_bounds m hQ.1).2.1
  exact_mod_cast hcut.trans ((Real.exp_le_exp.mpr (hQ.2.2.1.trans hnum)).trans
    (allocatedSiteScale_lower (G := G) B U b hR hσ hQ.1 he hE))

theorem allocatedKernelSiteScale_upper
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset α)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    {p Ebad T e E : ℝ}
    (hp : 0 ≤ p) (hEbad : 0 ≤ Ebad) (hT : 0 ≤ T) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p) :
    ((allocatedKernelSiteScale (G := G) B U b hR hσ p Ebad T e E).value : ℝ) ≤
      Real.exp (allocatedSiteScaleLog m (allocatedKernelSiteParameter p Ebad T) e E) := by
  have hQ := allocatedKernelSiteParameter_bounds hp hEbad hT
  exact allocatedSiteScale_upper (G := G) B U b hR hσ rows hq hinj hQ.1 he hE
    (hvars.trans hQ.2.1) (fun j => (hI j).trans hQ.2.1) (fun j => (hn j).trans hQ.2.1)
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hQ.2.1))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hQ.2.1))

theorem allocatedKernelSiteScale_affine_bad_probability [DecidableEq G]
    {dim : ℕ} [Nonempty (Fin dim)] {p Ebad T e E : ℝ}
    (hp : 0 ≤ p) (hEbad : 0 ≤ Ebad) (hT : 0 ≤ T) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdim : (dim : ℝ) ≤ p) (hGp : (Fintype.card G : ℝ) ≤ p)
    (hG : dim * (dim + 2) ≤ Fintype.card G) (selection : Fin dim ↪ G)
    {M D : ℕ} (hM : 0 < M) (hD : 0 < D)
    (hMT : (M : ℝ) ≤ Real.exp T) (hDp : (D : ℝ) ≤ Real.exp p) :
    let S := allocatedKernelSiteScale (G := G) B U b hR hσ p Ebad T e E
    let η := Real.exp (-(Ebad + 1))
    let cutoff := scalarKernelCutoff (Fin dim) G M D η
    let hlarge := (allocatedKernelSiteScale_cutoff B U b hR hσ hp hEbad hT he hE hdim hGp hM hD hMT hDp).2.2
    ∀ (K : G → ℕ) (hKL : ∀ g, K g ≤ S.value) (hDK : ∀ g, S.value ≤ D * K g)
      (c : G → ℤ) (moduli : G → Option (Fin dim) → ℕ)
      (residues : ∀ g i, ZMod (moduli g i))
      (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliM : ∀ g i, moduli g i ≤ M),
    (FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights (Fin dim) S.value (K g) M D (c g) S.positive (hKL g) (hDK g)
        (moduli g) (residues g) (hmoduli g) (hmoduliM g)
        (scalarKernelCutoff_window_size (Fin dim) G hM hD (Real.exp_pos _) hlarge (hDK g)))).eventProbability
      (fun x => ¬ GoodScalarKernelTuple selection (1 / (cutoff : ℝ)) cutoff x) ≤ η := by
  intro S η cutoff hlarge K hKL hDK c moduli residues hmoduli hmoduliM
  exact affineKernel_explicit_probability_le_of_card_le (Fin dim) G
    (by simpa only [Fintype.card_fin] using hG) selection hM hD (Real.exp_pos _) S.positive
    hlarge K hKL hDK c moduli residues hmoduli hmoduliM

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {dim : ℕ} [Nonempty (Fin dim)] {p Ebad T e E : ℝ} {M D : ℕ}

local notation "siteScale" => allocatedKernelSiteScale (G := G) B U b hR hσ p Ebad T e E
local notation "cutoff" => scalarKernelCutoff (Fin dim) G M D (Real.exp (-(Ebad + 1)))
local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value siteScale)
local notation "sides" => allocatedPrincipalSides B U b siteScale

theorem allocatedKernelSiteScale_refined_window_size
    (hp : 0 ≤ p) (hEbad : 0 ≤ Ebad) (hT : 0 ≤ T) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdim : (dim : ℝ) ≤ p) (hGp : (Fintype.card G : ℝ) ≤ p)
    (hM : 0 < M) (hD : 0 < D) (hMT : (M : ℝ) ≤ Real.exp T) (hDp : (D : ℝ) ≤ Real.exp p)
    (hdimSmall : dim ≤ m + 1) (a : Fin cutoff)
    {X : Type*} [Fintype X] (hX : (Fintype.card X : ℝ) ≤ p)
    (q : X → ℕ) (hq : ∀ x, (q x : ℝ) ≤ Real.exp p) :
    ∀ ax, (Fintype.card (Fin dim) + 1) * residueRefinedPeriod (kernelPeriodCandidate (m + 1) a) q ≤
      principalAxisLength (fun ax => ¬grid ax) sides ax := by
  have hc := (allocatedKernelSiteScale_cutoff B U b hR hσ hp hEbad hT he hE
    hdim hGp hM hD hMT hDp).2.1
  have hperiod := kernelPeriodCandidate_le_exp hc (m + 1) a
  have hrefined := residueRefinedPeriod_exp_bound (kernelPeriodCandidate (m + 1) a) q hperiod hq
  have hdimExp : ((dim + 1 : ℕ) : ℝ) ≤ Real.exp (dim + 1 : ℕ) := by
    linarith [Real.add_one_le_exp ((dim + 1 : ℕ) : ℝ)]
  have hbudget := allocatedKernelSiteParameter_refined_budget m hdimSmall hp hEbad hT
  have hprod := mul_le_mul_of_nonneg_right hX hp
  have hcost : ((dim + 1 : ℕ) : ℝ) +
      ((m + 1 : ℕ) * allocatedKernelPrimitiveBudget p Ebad T + Fintype.card X * p) ≤
        allocatedSiteScaleNumeric m (allocatedKernelSiteParameter p Ebad T) := by nlinarith
  have hsize : ((dim + 1 : ℕ) : ℝ) * residueRefinedPeriod (kernelPeriodCandidate (m + 1) a) q ≤
      (LayerSamplerScale.value siteScale : ℝ) := by
    calc
      _ ≤ Real.exp (dim + 1 : ℕ) *
          Real.exp ((m + 1 : ℕ) * allocatedKernelPrimitiveBudget p Ebad T + Fintype.card X * p) :=
        mul_le_mul hdimExp hrefined (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (((dim + 1 : ℕ) : ℝ) +
          ((m + 1 : ℕ) * allocatedKernelPrimitiveBudget p Ebad T + Fintype.card X * p)) :=
        (Real.exp_add _ _).symm
      _ ≤ Real.exp (allocatedSiteScaleNumeric m (allocatedKernelSiteParameter p Ebad T)) :=
        Real.exp_le_exp.mpr hcost
      _ ≤ _ := allocatedSiteScale_lower (G := G) B U b hR hσ
        (allocatedKernelSiteParameter_bounds hp hEbad hT).1 he hE
  intro ax
  rw [allocatedPrincipalSides_long_restricted]
  simpa only [Fintype.card_fin] using
    (show (dim + 1) * residueRefinedPeriod (kernelPeriodCandidate (m + 1) a) q ≤
      LayerSamplerScale.value siteScale by exact_mod_cast hsize)

variable [∀ j, DecidableEq (I j)] [∀ ax, DecidableEq (B ax)]
local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : jets j → Finset (Fin dim)))

theorem exists_allocatedKernelSiteScale_refined_residue_data
    (hp : 0 ≤ p) (hEbad : 0 ≤ Ebad) (hT : 0 ≤ T) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdim : (dim : ℝ) ≤ p) (hGp : (Fintype.card G : ℝ) ≤ p)
    (hM : 0 < M) (hD : 0 < D) (hMT : (M : ℝ) ≤ Real.exp T) (hDp : (D : ℝ) ≤ Real.exp p)
    (hdimSmall : dim ≤ m + 1) (a : Fin cutoff)
    {X : Type*} [Fintype X] (hX : (Fintype.card X : ℝ) ≤ p)
    (q : X → ℕ) (hq : ∀ x, 0 < q x) (hqp : ∀ x, (q x : ℝ) ≤ Real.exp p)
    (x : G → IntegerScalarCubeBox (Fin dim) (LayerSamplerScale.value siteScale)) :
    let modulus := kernelPeriodCandidate (m + 1) a
    let refined := residueRefinedPeriod modulus q
    ∃ (hRefined : 0 < refined)
      (hsize : ∀ ax, (Fintype.card (Fin dim) + 1) * refined ≤
        principalAxisLength (fun ax => ¬grid ax) sides ax)
      (reference : PrincipalAxisTuples (α := Fin dim) grid sides →
        (PrincipalTupleIndex (fun ax : {ax // ¬grid ax} => B ax.val)
          (fun ax => layerSamplerDegree I n ax.val) → Option (Fin dim) → ZMod refined) →
        PrincipalAxisTuples (α := Fin dim) (fun ax => ¬grid ax) sides)
      (residue : PrincipalAxisTuples (α := Fin dim) grid sides →
        (PrincipalTupleIndex (fun ax : {ax // ¬grid ax} => B ax.val)
          (fun ax => layerSamplerDegree I n ax.val) → Option (Fin dim) → ZMod refined) →
        ∀ j, Matrix (jets j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
      (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
      (∀ u r v, (allocatedLongResidueWeights B U b siteScale refined hRefined r hsize).weight v ≠ 0 →
        ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b siteScale x u jetRows j v) modulus =
          residue u r j) := by
  intro modulus refined
  have hRefined : 0 < refined := residueRefinedPeriod_pos (kernelPeriodCandidate_pos (m + 1) a) q hq
  have hsize := allocatedKernelSiteScale_refined_window_size B U b hR hσ hp hEbad hT he hE
    hdim hGp hM hD hMT hDp hdimSmall a hX q hqp
  refine ⟨hRefined, hsize, ?_⟩
  exact allocated_refined_residue_data B U b siteScale x jetRows hRefined
    ⟨∏ t, q t, rfl⟩ hsize

end Erdos3.VectorPolynomial

end

end OAI
