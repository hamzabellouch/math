import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

variable (t : ℕ) (ht : ∀ j : Fin m, j.val + 1 ≤ t)

noncomputable def allocatedLayerIntegerPMFsWithTailDegree (j : Fin m) :
    Fin (n j) → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → PMF ℤ :=
  allocatedProjectionPMFs (euclideanSubspace (U j)) (b j) (layerIntegerPrincipalSlots B j)
    (constantCoefficientSlot _ _) (j.val + 1) S.value t (Nat.zero_lt_succ _) S.positive
    (layerSamplerBox B U b S) (layerSamplerBox_one_le B U b S) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (ht j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j) (S.width j)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

include hR hσ in
theorem allocatedLayerColumnsWithTailDegree_chart (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (j : Fin m) (d) (x) (hx : mixedCoefficientDensity (fun i => allocatedLayerCenters B U b S j i d)
      (fun i => allocatedLayerWidths B U b S j i d)
      (fun i => allocatedLayerIntegerPMFsWithTailDegree B U b hR hσ S t ht j i d) x ≠ 0) :
    normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) ∈
      standardLatticeSmallBox (J j) := by
  exact allocatedArrayColumns_chart (euclideanSubspace (U j)) (b j) (layerIntegerPrincipalSlots B j)
    (constantCoefficientSlot _ _) (j.val + 1) S.value t (Nat.zero_lt_succ _) S.positive
    (layerSamplerBox B U b S) (layerSamplerBox_one_le B U b S) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (ht j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j) (S.width j)
    (layerContinuousPrincipalSlots B j) (o j) (layerContinuousPrincipalSlots_not_constant B j)
    (layerIntegerPrincipalSlots_not_constant B j) rfl (hσ1 j)
    (layerSamplerSides_integer_principal B U b R S.value j) (hC j) (hchart j) (hsmall j) d x hx

theorem allocatedLayerSupportedWithTailDegree_polynomial_chart (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (j : Fin m) (a) (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFsWithTailDegree B U b hR hσ S t ht j) a)
    (x : LayerSamplerVariables G I n B → ℝ) (hx : ∀ v, |x v| ≤ layerSamplerBox B U b S v) :
    mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x ∈
      standardLatticeSmallBox (J j) := by
  exact allocatedArraySupported_polynomial_chart (euclideanSubspace (U j)) (b j) (layerIntegerPrincipalSlots B j)
    (constantCoefficientSlot _ _) (j.val + 1) S.value t (Nat.zero_lt_succ _) S.positive
    (layerSamplerBox B U b S) (layerSamplerBox_one_le B U b S) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (ht j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j) (S.width j)
    (layerContinuousPrincipalSlots B j) (o j) (layerContinuousPrincipalSlots_not_constant B j)
    (layerIntegerPrincipalSlots_not_constant B j) rfl (hσ1 j)
    (layerSamplerSides_integer_principal B U b R S.value j) (hC j) (hchart j) (hsmall j) a ha x hx

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (t : ℕ) (ht : ∀ j : Fin m, j.val + 1 ≤ t) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)

theorem allocatedLayerIntegerWithTailDegree_moderate_tail_zero
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(t+1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFsWithTailDegree B U basis hR hσ S t ht j i d).support)
    (d : Slots) (hd₀ : d ≠ constantCoefficientSlot _ _)
    (hdP : d ∉ layerIntegerPrincipalSlots B j i) : a d = 0 := by
  exact allocatedIntegerCoordinate_tail_zero (layerIntegerPrincipalSlots B j i)
    (constantCoefficientSlot _ _) (j.val+1) (basisAxisScale (basis j) i) S.value t
    (Nat.zero_lt_succ _) (basisAxisScale_pos (basis j) i) S.positive
    (layerSamplerBox B U basis S)
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (layerSamplerBox_le B U basis S) Subtype.val
    (fun e => e.property.trans (ht j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j i) (S.width j) hmoderate d hd₀ hdP (ha d)

theorem allocatedLayerIntegerWithTailDegree_moderate_eval
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(t+1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFsWithTailDegree B U basis hR hσ S t ht j i d).support)
    (x : LayerSamplerVariables G I n B → ℤ) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      a (constantCoefficientSlot _ _) + ∑ b : B ⟨j, Sum.inr i⟩,
        a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
          ∏ v : Fin (j.val+1), x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) := by
  exact integerPrincipalPolynomial_eval (layerSamplerDegree I n) ⟨j, Sum.inr i⟩
    (Nat.zero_lt_succ _) a
    (allocatedLayerIntegerWithTailDegree_moderate_tail_zero B U basis hR hσ S t ht j i
      hmoderate a ha) x

theorem allocatedLayerIntegerWithTailDegree_moderate_eval_congr
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(t+1))
    (a a' : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFsWithTailDegree B U basis hR hσ S t ht j i d).support)
    (ha' : ∀ d, a' d ∈ (allocatedLayerIntegerPMFsWithTailDegree B U basis hR hσ S t ht j i d).support)
    (hconstant : a (constantCoefficientSlot _ _) = a' (constantCoefficientSlot _ _))
    (hcoeff : ∀ b : B ⟨j, Sum.inr i⟩,
      a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) =
        a' (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))
    (x x' : LayerSamplerVariables G I n B → ℤ)
    (hprincipal : ∀ (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val+1)),
      x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) = x' (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩)) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      MvPolynomial.eval x' (integerMonomialArrayPolynomial Subtype.val a') := by
  rw [allocatedLayerIntegerWithTailDegree_moderate_eval B U basis hR hσ S t ht j i
    hmoderate a ha x,
    allocatedLayerIntegerWithTailDegree_moderate_eval B U basis hR hσ S t ht j i
      hmoderate a' ha' x', hconstant]
  simp only [hcoeff, hprincipal]

theorem allocatedLayerIntegerWithTailDegree_moderateJet_congr
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(t+1))
    (a a' : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFsWithTailDegree B U basis hR hσ S t ht j i d).support)
    (ha' : ∀ d, a' d ∈ (allocatedLayerIntegerPMFsWithTailDegree B U basis hR hσ S t ht j i d).support)
    (hconstant : a (constantCoefficientSlot _ _) = a' (constantCoefficientSlot _ _))
    (hcoeff : ∀ b : B ⟨j, Sum.inr i⟩,
      a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) =
        a' (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))
    {α O : Type*} [DecidableEq α]
    (vertices vertices' : Finset α → LayerSamplerVariables G I n B → ℤ)
    (rows : O → Finset α)
    (hprincipal : ∀ o row, row ∈ (rows o).powerset →
      ∀ (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val+1)),
        vertices row (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) =
          vertices' row (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩)) :
    integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ)) vertices rows *ᵥ a =
      integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ)) vertices' rows *ᵥ a' := by
  funext o
  simp only [integerJetMatrix_apply_coefficients, MvPolynomial.C_mul_monomial, mul_one]
  change booleanCoefficient (fun row => MvPolynomial.eval (vertices row)
      (integerMonomialArrayPolynomial Subtype.val a)) (rows o) =
    booleanCoefficient (fun row => MvPolynomial.eval (vertices' row)
      (integerMonomialArrayPolynomial Subtype.val a')) (rows o)
  unfold booleanCoefficient
  apply Finset.sum_congr rfl
  intro row hrow
  exact congrArg (fun v : ℤ => (-1) ^ (rows o \ row).card * v)
    (allocatedLayerIntegerWithTailDegree_moderate_eval_congr B U basis hR hσ S t ht j i
      hmoderate a a' ha ha' hconstant hcoeff (vertices row) (vertices' row) (hprincipal o row hrow))

theorem allocatedLayerModerateIntegerImageWithTailDegree_freeze
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(t+1))
    {X α O : Type*} [DecidableEq α]
    (a : X → Slots → ℤ)
    (vertices : X → Finset α → LayerSamplerVariables G I n B → ℤ)
    (rows : O → Finset α) (center : O → ℤ) (x x' : X)
    (ha : ∀ d, a x d ∈ (allocatedLayerIntegerPMFsWithTailDegree B U basis hR hσ S t ht j i d).support)
    (ha' : ∀ d, a x' d ∈ (allocatedLayerIntegerPMFsWithTailDegree B U basis hR hσ S t ht j i d).support)
    (hconstant : a x (constantCoefficientSlot _ _) = a x' (constantCoefficientSlot _ _))
    (hcoeff : ∀ b : B ⟨j, Sum.inr i⟩,
      a x (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) =
        a x' (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))
    (hprincipal : ∀ o row, row ∈ (rows o).powerset →
      ∀ (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val+1)),
        vertices x row (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) =
          vertices x' row (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩)) :
    integerArrayJetImage Subtype.val a vertices rows center x =
      integerArrayJetImage Subtype.val a vertices rows center x' := by
  unfold integerArrayJetImage
  rw [allocatedLayerIntegerWithTailDegree_moderateJet_congr B U basis hR hσ S t ht j i hmoderate
    (a x) (a x') ha ha' hconstant hcoeff (vertices x) (vertices x') rows hprincipal]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

def allocatedGridAxisWithTailDegree (t L : ℕ) : LayerSamplerAxis I n → Prop
  | ⟨_, .inl _⟩ => False
  | ⟨j, .inr i⟩ => basisAxisScale (basis j) i ≤ L^(t+1)

noncomputable instance allocatedGridAxisWithTailDegreeDecidable (t L : ℕ) :
    DecidablePred (allocatedGridAxisWithTailDegree (I := I) U basis t L) := Classical.decPred _

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

variable (t : ℕ) (ht : ∀ j : Fin m, j.val + 1 ≤ t)

include ht

theorem allocatedPrincipalSidesWithTailDegree_long (d : LayerSamplerAxis I n)
    (hd : ¬allocatedGridAxisWithTailDegree U basis t S.value d) (b : B d) (v : Fin (layerSamplerDegree I n d)) :
    allocatedPrincipalSides B U basis S ⟨d, b, v⟩ = S.value := by
  rcases d with ⟨j, d⟩
  cases d with
  | inl i => rfl
  | inr i =>
    change ¬basisAxisScale (basis j) i ≤ S.value^(t+1) at hd
    have hactive : S.value^(j.val+1) < basisAxisScale (basis j) i :=
      (Nat.pow_le_pow_right S.positive
        ((ht j).trans (Nat.le_succ _))).trans_lt (Nat.lt_of_not_ge hd)
    simp only [allocatedPrincipalSides, layerSamplerSides, heterogeneousSamplerSides,
      layerSamplerDenominators, Sum.elim_inr, layerSamplerDegree,
      integerAxisSideLength, hactive, ↓reduceIte]

local notation "gridAxes" => allocatedGridAxisWithTailDegree (I := I) U basis t (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "degree" => layerSamplerDegree I n

theorem allocatedPrincipalSidesWithTailDegree_long_restricted
    (j : PrincipalTupleIndex (fun d : {d // ¬gridAxes d} => B d.val) (fun d => degree d.val)) :
    principalAxisLength (fun d => ¬gridAxes d) sides j = S.value :=
  allocatedPrincipalSidesWithTailDegree_long B U basis S t ht j.1.val j.1.property j.2.1 j.2.2

section Law

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem allocatedPrincipalWithTailDegree_partition_residues (M : ℕ) [NeZero M] (hM : 0 < M)
    (hsize : (Fintype.card α+1)*M ≤ S.value)
    (f : PrincipalIntegerTuples B degree α sides → ℂ) :
    (principalTupleWeights B degree sides (allocatedPrincipalSides_pos B U basis S)).complexMean f =
      (principalTupleWeights (fun d : {d // gridAxes d} => B d.val) (fun d => degree d.val)
        (principalAxisLength gridAxes sides)
        (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩)).complexMean (fun u =>
      ((principalTupleWeights (α := α) (fun d : {d // ¬gridAxes d} => B d.val) (fun d => degree d.val)
        (principalAxisLength (fun d => ¬gridAxes d) sides)
        (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩)).fiberLaw
          (principalResidueLabel M)).complexMean (fun r =>
      (principalResidueWeights (fun d : {d // ¬gridAxes d} => B d.val) (fun d => degree d.val)
        (principalAxisLength (fun d => ¬gridAxes d) sides)
        (fun j => allocatedPrincipalSides_pos B U basis S ⟨j.1.val, j.2⟩) M hM r
        (fun j => by rw [allocatedPrincipalSidesWithTailDegree_long_restricted B U basis S t ht j]; exact hsize)).complexMean
          (fun v => f (principalAxisJoin gridAxes u v)))) := by
  exact principalTupleWeights_partition_residues gridAxes sides
    (allocatedPrincipalSides_pos B U basis S) M hM
    (fun j => by rw [allocatedPrincipalSidesWithTailDegree_long_restricted B U basis S t ht j]; exact hsize) f

end Law

theorem allocatedGridAxisWithTailDegree_jet_frozen
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (j : Fin m) (i : Fin (n j)) (hgrid : gridAxes ⟨j, Sum.inr i⟩)
    (a : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFsWithTailDegree B U basis hR hσ S t ht j i d).support)
    {Z α O : Type*} [DecidableEq α] (extra : G → Option α → Z)
    (z : Z ⊕ PrincipalAxisParameter (B := B) (h := degree) (α := α) gridAxes → ℤ)
    (x y : PrincipalAxisParameter (B := B) (h := degree) (α := α) (fun d => ¬gridAxes d) → ℤ)
    (rows : O → Finset α) :
    integerMappedJetMatrix Subtype.val (partitionedPrincipalInput gridAxes extra) z rows x *ᵥ a =
      integerMappedJetMatrix Subtype.val (partitionedPrincipalInput gridAxes extra) z rows y *ᵥ a := by
  apply allocatedLayerIntegerWithTailDegree_moderateJet_congr B U basis hR hσ S t ht j i hgrid
    a a ha ha rfl (fun _ => rfl)
    (integerMappedCubeTuple (partitionedPrincipalInput gridAxes extra) z x)
    (integerMappedCubeTuple (partitionedPrincipalInput gridAxes extra) z y) rows
  intro o t _ b v
  exact partitionedPrincipalInput_frozen_cube gridAxes extra z x y t ⟨j, Sum.inr i⟩ hgrid b v

end Erdos3.VectorPolynomial

end

end OAI
