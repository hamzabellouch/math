import OAI.Analysis.Naimark.Peaking

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

abbrev Corner := MatrixHNNCorner B.embedBase
instance modelCornerCStarAlgebra : CStarAlgebra B.Corner := inferInstance
abbrev cornerBase := matrixCornerBase B.embedBase

theorem cornerBase_injective : Function.Injective B.cornerBase :=
  matrixCornerBase_injective B.embedBase (atomicEmbedding_injective B.atoms false)

theorem corner_unique (hs : B.Separated) (hA : IsSimpleCStar A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) : StateExtensionUnique B.cornerBase f :=
  corner_unique_of_matrix B.embedBase f (B.supported_matrix_unique hs hA f hf false)

theorem corner_unique_pure_extension (hs : B.Separated) (hA : IsSimpleCStar A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ g : B.Corner →L[ℂ] ℂ, IsPureState g ∧ restrictState B.cornerBase g = f ∧
      ∀ h : B.Corner →L[ℂ] ℂ, IsState h → restrictState B.cornerBase h = f → h = g :=
  (B.corner_unique hs hA f hf).exists_unique_pure B.cornerBase_injective hf

abbrev stableUnitary : unitary B.Corner :=
  matrixStableUnitary B.embedBase B.embedAux
    (matrixDiagonal_units B.embedBase B.embedAux B.diagonal B.model_diagonal_agree)

theorem stable_conjugates_peak (n : ℕ) :
    (B.stableUnitary:B.Corner)*B.cornerBase (B.peak false n)*star (B.stableUnitary:B.Corner) =
      B.cornerBase (B.peak true n) := by
  have hh := matrixStable_conjugates B.embedBase B.embedAux B.diagonal
    B.model_diagonal_agree (B.tail n)
  simpa only [stableUnitary,matrixStableUnitary,cornerBase,B.diagonal_tail] using hh

end PeakingPairData

open scoped CStarAlgebra Matrix
section
variable {A Z : Type*} [CStarAlgebra A] [CStarAlgebra Z]
    (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)

def matrixCornerEntry (i j : Bool) : Z →L[ℂ] MatrixHNNCorner φ where
  toFun z := ⟨φ (matrixSingle false i 1) * z * φ (matrixSingle j false 1), by
    constructor
    · change φ (matrixSingle false false 1) * (φ _ * z * φ _) = _
      rw [← mul_assoc, ← mul_assoc, ← map_mul, matrixSingle_mul, one_mul]
    · change (φ _ * z * φ _) * φ (matrixSingle false false 1) = _
      rw [mul_assoc, ← map_mul, matrixSingle_mul, one_mul]⟩
  map_add' x y := Subtype.ext (by dsimp; simp only [mul_add,add_mul])
  map_smul' c z := Subtype.ext (by dsimp; simp only [mul_smul_comm, smul_mul_assoc])
  cont := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_id).mul continuous_const

@[simp] theorem matrixCornerEntry_coe (i j : Bool) (z : Z) :
    (matrixCornerEntry φ i j z : Z) =
      φ (matrixSingle false i 1) * z * φ (matrixSingle j false 1) := rfl

@[simp] theorem matrixCornerEntry_corner (z : MatrixHNNCorner φ) :
    matrixCornerEntry φ false false (z : Z) = z := by
  apply Subtype.ext
  exact (congrArg (· * matrixCornerProjection φ) z.2.1).trans z.2.2

theorem matrix_diag_sum_one :
    matrixSingle false false (1:A) + matrixSingle true true 1 = 1 := by
  ext i j
  cases i <;> cases j <;> simp [matrixSingle_apply]

theorem matrixCornerEntry_mul (i j : Bool) (x y : Z) :
    matrixCornerEntry φ i j (x*y) =
      matrixCornerEntry φ i false x * matrixCornerEntry φ false j y +
      matrixCornerEntry φ i true x * matrixCornerEntry φ true j y := by
  apply Subtype.ext
  change φ (matrixSingle false i 1) * (x*y) * φ (matrixSingle j false 1) =
    (φ (matrixSingle false i 1) * x * φ (matrixSingle false false 1)) *
      (φ (matrixSingle false false 1) * y * φ (matrixSingle j false 1)) +
    (φ (matrixSingle false i 1) * x * φ (matrixSingle true false 1)) *
      (φ (matrixSingle false true 1) * y * φ (matrixSingle j false 1))
  symm
  calc
    _ = φ (matrixSingle false i 1) * x *
        (φ (matrixSingle false false 1) * φ (matrixSingle false false 1) +
         φ (matrixSingle true false 1) * φ (matrixSingle false true 1)) *
        y * φ (matrixSingle j false 1) := by noncomm_ring
    _ = _ := by
      rw [← map_mul, ← map_mul, matrixSingle_mul, matrixSingle_mul, one_mul,
        ← map_add, matrix_diag_sum_one, map_one]
      simp only [mul_one, mul_assoc]

@[simp] theorem matrixCornerEntry_star (i j : Bool) (x : Z) :
    matrixCornerEntry φ i j (star x) = star (matrixCornerEntry φ j i x) := by
  apply Subtype.ext
  change φ (matrixSingle false i 1) * star x * φ (matrixSingle j false 1) =
    star (φ (matrixSingle false j 1) * x * φ (matrixSingle i false 1))
  simp only [star_mul, ← map_star, matrixSingle_star, star_one, mul_assoc]

theorem matrixSingle_sandwich (i j : Bool) (M : CStarMatrix Bool Bool A) :
    matrixSingle false i 1 * M * matrixSingle j false 1 =
      matrixSingle false false (M i j) := by
  calc
    _ = matrixSingle false i 1 *
        (matrixSingle i i 1 * M * matrixSingle j j 1) * matrixSingle j false 1 := by
      symm
      calc
        _ = (matrixSingle false i 1 * matrixSingle i i 1) * M *
            (matrixSingle j j 1 * matrixSingle j false 1) := by simp only [mul_assoc]
        _ = _ := by rw [matrixSingle_mul,matrixSingle_mul,one_mul]
    _ = _ := by
      rw [matrixSingle_compress,one_mul,mul_one,matrixSingle_mul,one_mul,
        matrixSingle_mul,mul_one]

@[simp] theorem matrixCornerEntry_base (i j : Bool) (M : CStarMatrix Bool Bool A) :
    matrixCornerEntry φ i j (φ M) = matrixCornerBase φ (M i j) := by
  apply Subtype.ext
  change φ (matrixSingle false i 1) * φ M * φ (matrixSingle j false 1) =
    φ (matrixSingle false false (M i j))
  rw [← map_mul, ← map_mul, matrixSingle_sandwich]

@[simp] theorem matrixCornerEntry_one (i j : Bool) :
    matrixCornerEntry φ i j 1 = matrixCornerBase φ ((1 : CStarMatrix Bool Bool A) i j) := by
  rw [← map_one φ, matrixCornerEntry_base]

end

open scoped CStarAlgebra
section
variable {A D Z : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra Z]
    (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)

def matrixEntrySubalgebra (S : StarSubalgebra ℂ (MatrixHNNCorner φ)) : StarSubalgebra ℂ Z where
  carrier := {z | ∀ i j, matrixCornerEntry φ i j z ∈ S}
  zero_mem' := by intro i j; rw [map_zero]; exact zero_mem S
  add_mem' := by intro x y hx hy i j; rw [map_add]; exact add_mem (hx i j) (hy i j)
  mul_mem' := by
    intro x y hx hy i j
    rw [matrixCornerEntry_mul]
    exact S.add_mem (S.mul_mem (hx i false) (hy false j)) (S.mul_mem (hx i true) (hy true j))
  algebraMap_mem' c := by
    intro i j
    rw [Algebra.algebraMap_eq_smul_one, map_smul, matrixCornerEntry_one]
    apply S.smul_mem
    cases i <;> cases j <;> simp
  star_mem' := by
    intro x hx i j
    rw [matrixCornerEntry_star]
    exact star_mem (hx j i)

@[simp] theorem mem_matrixEntrySubalgebra (S : StarSubalgebra ℂ (MatrixHNNCorner φ)) (z : Z) :
    z ∈ matrixEntrySubalgebra φ S ↔ ∀ i j, matrixCornerEntry φ i j z ∈ S := Iff.rfl

theorem matrixEntrySubalgebra_closed (S : StarSubalgebra ℂ (MatrixHNNCorner φ))
    (hS : IsClosed (S : Set (MatrixHNNCorner φ))) :
    IsClosed (matrixEntrySubalgebra φ S : Set Z) := by
  change IsClosed {z | ∀ i j, matrixCornerEntry φ i j z ∈ S}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    hS.preimage (matrixCornerEntry φ i j).continuous

theorem matrixCorner_generated_of_entries (T : Set Z)
    (hd : Dense (StarAlgebra.adjoin ℂ T : Set Z))
    (S : StarSubalgebra ℂ (MatrixHNNCorner φ))
    (hS : IsClosed (S : Set (MatrixHNNCorner φ)))
    (hentries : ∀ z ∈ T, ∀ i j, matrixCornerEntry φ i j z ∈ S) : S = ⊤ := by
  have hsub : StarAlgebra.adjoin ℂ T ≤ matrixEntrySubalgebra φ S := by
    exact StarAlgebra.adjoin_le (fun z hz => hentries z hz)
  have hall : ∀ z : Z, z ∈ matrixEntrySubalgebra φ S := by
    intro z
    apply (matrixEntrySubalgebra_closed φ S hS).closure_subset
    exact closure_mono hsub (hd z)
  apply eq_top_iff.mpr
  intro z _
  have h := hall (z:Z) false false
  simpa only [matrixCornerEntry_corner] using h

variable (ψ : CStarMatrix Bool Bool D →⋆ₐ[ℂ] Z)
    (diag : ∀ i : Bool, φ (matrixSingle i i (1 : A)) = ψ (matrixSingle i i (1 : D)))

include diag in

theorem matrixCornerEntry_letter_false (i j : Bool) :
    matrixCornerEntry φ i j (bridgeLetter ψ false) =
      if i = false ∧ j = true then star (matrixStable φ ψ diag) else 0 := by
  apply Subtype.ext
  change φ (matrixSingle false i 1) * ψ (matrixSingle false true 1) *
    φ (matrixSingle j false 1) = _
  have hs : ψ (matrixSingle false true (1:D)) =
      φ (matrixSingle false false 1) * ψ (matrixSingle false true 1) *
        φ (matrixSingle true true 1) := by
    rw [diag false,diag true,← map_mul,← map_mul,matrixSingle_mul,matrixSingle_mul,one_mul,one_mul]
  rw [hs]
  have hgroup : φ (matrixSingle false i 1) *
      (φ (matrixSingle false false 1) * ψ (matrixSingle false true 1) * φ (matrixSingle true true 1)) *
      φ (matrixSingle j false 1) =
    (φ (matrixSingle false i 1) * φ (matrixSingle false false 1)) * ψ (matrixSingle false true 1) *
      (φ (matrixSingle true true 1) * φ (matrixSingle j false 1)) := by simp only [mul_assoc]
  rw [hgroup,← map_mul,← map_mul]
  have hz₁ : matrixSingle false true (1:A) * matrixSingle false false 1 = 0 :=
    matrixSingle_mul_of_ne _ _ _ _ _ _ (by decide)
  have hz₂ : matrixSingle true true (1:A) * matrixSingle false false 1 = 0 :=
    matrixSingle_mul_of_ne _ _ _ _ _ _ (by decide)
  cases i <;> cases j <;> simp [hz₁,hz₂]
  change φ (matrixSingle false false 1) * ψ (matrixSingle false true 1) *
    φ (matrixSingle true false 1) = star (φ (matrixSingle false true 1) * ψ (matrixSingle true false 1))
  rw [diag false,← map_mul,matrixSingle_mul,one_mul]
  simp only [star_mul,← map_star,matrixSingle_star,star_one]

include diag in
theorem matrixCornerEntry_letter_true (i j : Bool) :
    matrixCornerEntry φ i j (bridgeLetter ψ true) =
      if j = false ∧ i = true then matrixStable φ ψ diag else 0 := by
  rw [show bridgeLetter ψ true = star (bridgeLetter ψ false) by
    simp, matrixCornerEntry_star,
    matrixCornerEntry_letter_false φ ψ diag j i]
  split_ifs <;> simp

def matrixCornerLetter (i : Bool) : MatrixHNNCorner φ :=
  if i then matrixStable φ ψ diag else star (matrixStable φ ψ diag)

@[simp] theorem matrixCornerLetter_star (i : Bool) :
    star (matrixCornerLetter φ ψ diag i) = matrixCornerLetter φ ψ diag (!i) := by
  cases i <;> simp [matrixCornerLetter]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D]
  (δ : Bool → D →⋆ₐ[ℂ] A)
  (hd : ∀ x, φ (matrixDiagonalHom δ x) =
    ψ (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D) x))

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in

theorem matrixCorner_generators
    (hdense : Dense (Algebra.adjoin ℂ (Set.range φ ∪ Set.range ψ) : Set Z)) :
    Dense (StarAlgebra.adjoin ℂ
      (Set.range (matrixCornerBase φ) ∪ Set.range (matrixCornerLetter φ ψ diag)) :
        Set (MatrixHNNCorner φ)) := by
  let T := StarAlgebra.adjoin ℂ
    (Set.range (matrixCornerBase φ) ∪ Set.range (matrixCornerLetter φ ψ diag))
  let S := T.topologicalClosure
  have hbase (a : A) : matrixCornerBase φ a ∈ S :=
    T.le_topologicalClosure (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a,rfl⟩))
  have hletter (i : Bool) : matrixCornerLetter φ ψ diag i ∈ S :=
    T.le_topologicalClosure (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨i,rfl⟩))
  rw [matrix_bridge_generators φ ψ δ hd] at hdense
  have hds : Dense (StarAlgebra.adjoin ℂ
      (Set.range φ ∪ Set.range (bridgeLetter ψ)) : Set Z) :=
    hdense.mono (Algebra.adjoin_le (StarAlgebra.subset_adjoin ℂ _))
  have htop : S = ⊤ := matrixCorner_generated_of_entries φ _ hds S
    T.isClosed_topologicalClosure (by
      rintro z (⟨M,rfl⟩ | ⟨k,rfl⟩) i j
      · rw [matrixCornerEntry_base]; exact hbase _
      · cases k
        · rw [matrixCornerEntry_letter_false φ ψ diag]
          split_ifs
          · exact hletter false
          · exact zero_mem S
        · rw [matrixCornerEntry_letter_true φ ψ diag]
          split_ifs
          · exact hletter true
          · exact zero_mem S)
  intro z
  change z ∈ S
  rw [htop]
  trivial

end

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

abbrev cornerLetter : Bool → B.Corner :=
  matrixCornerLetter B.embedBase B.embedAux
    (matrixDiagonal_units B.embedBase B.embedAux B.diagonal B.model_diagonal_agree)

@[simp] theorem cornerLetter_true : B.cornerLetter true = (B.stableUnitary : B.Corner) := rfl
@[simp] theorem cornerLetter_false : B.cornerLetter false = star (B.stableUnitary : B.Corner) := rfl
@[simp] theorem cornerLetter_star (i : Bool) : star (B.cornerLetter i) = B.cornerLetter (!i) :=
  matrixCornerLetter_star _ _ _ i

theorem corner_generated :
    Dense (StarAlgebra.adjoin ℂ (Set.range B.cornerBase ∪ Set.range B.cornerLetter) : Set B.Corner) :=
  matrixCorner_generators B.embedBase B.embedAux _ B.diagonal B.model_diagonal_agree
    B.model_factors_dense

end PeakingPairData

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
  (E : C →L[ℂ] CStarMatrix Bool Bool A)

def matrixCornerExpectation : MatrixHNNCorner φ →L[ℂ] A :=
  (matrixEntryCLM false).comp (E.comp (cornerSubalgebra (matrixCornerProjection φ)
    (matrixCornerProjection_isProjection φ)).subtypeL)

@[simp] theorem matrixCornerExpectation_apply (x : MatrixHNNCorner φ) :
    matrixCornerExpectation φ E x = E (x:C) false false := rfl

theorem matrixCornerExpectation_base (hfix : ∀ a, E (φ a) = a) (a : A) :
    matrixCornerExpectation φ E (matrixCornerBase φ a) = a := by
  change E (φ (matrixSingle false false a)) false false = a
  rw [hfix,matrixSingle_apply,ite_eq_left ⟨rfl,rfl⟩]

theorem matrixCornerExpectation_one (hfix : ∀ a, E (φ a) = a) :
    matrixCornerExpectation φ E 1 = 1 := by
  rw [← map_one (matrixCornerBase φ)]
  exact matrixCornerExpectation_base φ E hfix 1

theorem matrixCornerExpectation_norm (hbound : ∀ x, ‖E x‖ ≤ ‖x‖) (x : MatrixHNNCorner φ) :
    ‖matrixCornerExpectation φ E x‖ ≤ ‖x‖ :=
  (CStarMatrix.norm_entry_le_norm (M := E (x:C)) (i := false) (j := false)).trans (hbound x)

theorem matrixCornerExpectation_star (hstar : ∀ x, E (star x) = star (E x))
    (x : MatrixHNNCorner φ) :
    matrixCornerExpectation φ E (star x) = star (matrixCornerExpectation φ E x) := by
  change (E (star (x:C))) false false = star (E (x:C) false false)
  rw [hstar]
  rfl

theorem matrixCornerExpectation_supported
    (hleft : ∀ a x, E (φ a*x) = a*E x)
    (hright : ∀ x a, E (x*φ a) = E x*a) (x : MatrixHNNCorner φ) :
    E (x:C) = matrixSingle false false (matrixCornerExpectation φ E x) := by
  have h := x.property
  have hcomp : φ (matrixSingle false false (1:A))*(x:C)*
      φ (matrixSingle false false (1:A)) = (x:C) := by
    exact (congrArg (· * matrixCornerProjection φ) h.1).trans h.2
  calc
    _ = E (φ (matrixSingle false false (1:A))*(x:C)*
      φ (matrixSingle false false (1:A))) := congrArg E hcomp.symm
    _ = matrixSingle false false (1:A)*E (x:C)*matrixSingle false false (1:A) := by
      rw [hright,hleft]
    _ = _ := by rw [matrixSingle_compress,one_mul,mul_one]; rfl

theorem matrixCornerExpectation_faithful
    (hleft : ∀ a x, E (φ a*x) = a*E x)
    (hright : ∀ x a, E (x*φ a) = E x*a)
    (hfaith : ∀ x, E (star x*x) = 0 → x = 0)
    (x : MatrixHNNCorner φ) (hx : matrixCornerExpectation φ E (star x*x) = 0) : x = 0 := by
  apply Subtype.ext
  apply hfaith (x:C)
  have hh := matrixCornerExpectation_supported φ E hleft hright (star x*x)
  change E (star (x:C)*(x:C)) = _ at hh
  rw [hx,matrixSingle_zero] at hh
  exact hh

theorem matrixCornerExpectation_state (hfix : ∀ a, E (φ a) = a)
    (hbound : ∀ x, ‖E x‖ ≤ ‖x‖) (hstar : ∀ x, E (star x) = star (E x))
    (f : A →L[ℂ] ℂ) (hf : IsState f) :
    IsState (f.comp (matrixCornerExpectation φ E)) := by
  apply isState_of_unital_contractive_hermitian
  · change f (matrixCornerExpectation φ E 1) = 1
    rw [matrixCornerExpectation_one φ E hfix,((isState_iff f).mp hf).1]
  · intro a
    exact (state_norm_apply_le f hf _).trans (matrixCornerExpectation_norm φ E hbound a)
  · intro a
    change f (matrixCornerExpectation φ E (star a)) = star (f (matrixCornerExpectation φ E a))
    rw [matrixCornerExpectation_star φ E hstar,state_map_star f hf]

end

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

abbrev modelExpectation : B.Model →L[ℂ] CStarMatrix Bool Bool A :=
  atomicExpectation B.atoms B.amalgam false

def expectCorner : B.Corner →L[ℂ] A :=
  matrixCornerExpectation B.embedBase B.modelExpectation

theorem expectCorner_base (a : A) : B.expectCorner (B.cornerBase a) = a :=
  matrixCornerExpectation_base B.embedBase B.modelExpectation
    (atomicExpectation_factor B.atoms B.amalgam false) a

theorem expectCorner_one : B.expectCorner 1 = 1 :=
  matrixCornerExpectation_one B.embedBase B.modelExpectation
    (atomicExpectation_factor B.atoms B.amalgam false)

theorem expectCorner_norm (x : B.Corner) : ‖B.expectCorner x‖ ≤ ‖x‖ :=
  matrixCornerExpectation_norm B.embedBase B.modelExpectation
    (atomicExpectation_norm_le B.atoms B.amalgam false) x

theorem expectCorner_star (x : B.Corner) : B.expectCorner (star x) = star (B.expectCorner x) :=
  matrixCornerExpectation_star B.embedBase B.modelExpectation
    (atomicExpectation_star B.atoms B.amalgam false) x

theorem expectCorner_faithful (x : B.Corner) (hx : B.expectCorner (star x*x) = 0) : x = 0 :=
  matrixCornerExpectation_faithful B.embedBase B.modelExpectation
    (atomicExpectation_factor_mul B.atoms B.amalgam false)
    (atomicExpectation_mul_factor B.atoms B.amalgam false)
    (atomicExpectation_faithful B.atoms B.amalgam false) x hx

theorem expectCorner_state (f : A →L[ℂ] ℂ) (hf : IsState f) :
    IsState (f.comp B.expectCorner) :=
  matrixCornerExpectation_state B.embedBase B.modelExpectation
    (atomicExpectation_factor B.atoms B.amalgam false)
    (atomicExpectation_norm_le B.atoms B.amalgam false)
    (atomicExpectation_star B.atoms B.amalgam false) f hf

end PeakingPairData

open scoped CStarAlgebra
section
variable {A D Z : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra Z]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z) (ψ : CStarMatrix Bool Bool D →⋆ₐ[ℂ] Z)
  (diag : ∀ i : Bool, φ (matrixSingle i i (1:A)) = ψ (matrixSingle i i (1:D)))

theorem matrixCornerLetter_coe (i : Bool) :
    (matrixCornerLetter φ ψ diag i : Z) =
      φ (matrixSingle false i 1) * bridgeLetter ψ i *
        φ (matrixSingle (!i) false 1) := by
  cases i
  · change star (φ (matrixSingle false true 1)*ψ (matrixSingle true false 1)) =
      φ (matrixSingle false false 1) * ψ (matrixSingle false true 1) *
        φ (matrixSingle true false 1)
    simp only [star_mul,← map_star,matrixSingle_star,star_one]
    rw [diag false,← map_mul,matrixSingle_mul,one_mul]
  · change φ (matrixSingle false true 1)*ψ (matrixSingle true false 1) =
      φ (matrixSingle false true 1)*ψ (matrixSingle true false 1)*φ (matrixSingle false false 1)
    rw [mul_assoc,diag false,← map_mul,matrixSingle_mul,mul_one]

namespace HNNWord
variable {φ ψ diag}

def matrixCore : HNNWord A → BridgeCore (CStarMatrix Bool Bool A)
  | .single i _ => .single i
  | .cons i a w => w.matrixCore.cons i (matrixSingle (!i) w.first a)

def matrixFinal : HNNWord A → CStarMatrix Bool Bool A
  | .single i a => matrixSingle (!i) false a
  | .cons _ _ w => w.matrixFinal

theorem eval_matrix_core (w : HNNWord A) :
    ((w.eval (matrixCornerBase φ) (matrixCornerLetter φ ψ diag) : MatrixHNNCorner φ) : Z) =
      φ (matrixSingle false w.first 1) * w.matrixCore.eval φ (bridgeLetter ψ) * φ w.matrixFinal := by
  induction w with
  | single i a =>
    change (matrixCornerLetter φ ψ diag i : Z) * φ (matrixSingle false false a) = _
    rw [matrixCornerLetter_coe]
    change (φ (matrixSingle false i 1) * bridgeLetter ψ i * φ (matrixSingle (!i) false 1)) *
      φ (matrixSingle false false a) =
      φ (matrixSingle false i 1) * bridgeLetter ψ i * φ (matrixSingle (!i) false a)
    rw [mul_assoc,← map_mul,matrixSingle_mul,one_mul]
  | cons i a w ih =>
    change ((matrixCornerLetter φ ψ diag i : Z) * φ (matrixSingle false false a)) *
      (↑(w.eval (matrixCornerBase φ) (matrixCornerLetter φ ψ diag)) : Z) = _
    rw [matrixCornerLetter_coe,ih]
    change _ = φ (matrixSingle false i 1) *
      (w.matrixCore.cons i (matrixSingle (!i) w.first a)).eval φ (bridgeLetter ψ) * φ w.matrixFinal
    calc
      _ = φ (matrixSingle false i 1) * bridgeLetter ψ i *
          (φ (matrixSingle (!i) false 1) * φ (matrixSingle false false a) *
            φ (matrixSingle false w.first 1)) *
          w.matrixCore.eval φ (bridgeLetter ψ) * φ w.matrixFinal := by simp only [mul_assoc]
      _ = _ := by
        rw [← map_mul,← map_mul,matrixSingle_mul,matrixSingle_mul,one_mul,mul_one,
          BridgeCore.eval_cons]
        simp only [mul_assoc]

theorem matrixCore_centered (Q : Bool → A → Prop) (K : CStarMatrix Bool Bool A → Prop)
    (hK : ∀ i j a, i = j ∨ Q i a → K (matrixSingle (!i) j a))
    (w : HNNWord A) (hw : w.Reduced Q) : w.matrixCore.Centered K := by
  induction w with
  | single i a => trivial
  | cons i a w ih => exact w.matrixCore.centered_cons K i _ (hK i w.first a hw.1) (ih hw.2)
end HNNWord

end

open scoped InnerProductSpace lp
section
section Fock
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]
  {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  (π : ∀ i r, A i →⋆ₐ[ℂ]
    (ℓ²(ColumnIndex L i r, ℂ) →L[ℂ] ℓ²(ColumnIndex L i r, ℂ)))

theorem atomicFock_vacuum_away_ne {i j : I} (hij : i ≠ j) (a : A i) (z : ℓ²(V,ℂ)) :
    FockAway L j (atomicFockRepresentation L π i a (fockVacuum L z)) := by
  intro p hp
  have hpi : p.1 ≠ some i := by
    rw [hp]
    exact fun h => hij (Option.some.inj h).symm
  have h := atomicFock_creation L π i a (fockVacuum L z)
    (fockVacuum_away L z i) ⟨p,hpi⟩ none
  change atomicFockRepresentation L π i a (fockVacuum L z) p = _ at h
  rw [h,fockVacuum_away L z j p hp,zero_mul]

theorem fockAway_inner_starts (i : I) (x y : AtomicFockSpace L)
    (hx : FockAway L i x) (hy : FockStarts L i y) : inner ℂ x y = 0 := by
  rw [lp.inner_eq_tsum]
  suffices h : ∀ p, inner ℂ (x p) (y p) = 0 by simp only [h,tsum_zero]
  intro p
  by_cases hp : p.1 = some i
  · rw [hx p hp,inner_zero_left]
  · rw [hy p hp,inner_zero_right]
end Fock

variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
  (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]
  {i j : I} (hij : i ≠ j) (b : Bool → A j)
  (hb : ∀ v r, (d j).trace (((d j).atom r).1*b v*((d j).atom r).1) = 0)
  (K : A i → Prop)
  (hK : ∀ a, K a → ∀ r, (d i).trace (((d i).atom r).1*a*((d i).atom r).1) = 0)

omit [DecidableEq V] in
include hij hb hK in

theorem atomicCore_coefficient_zero (k : I) (w : BridgeCore (A i)) (hw : w.Centered K)
    (a c : A i) :
    inner ℂ (atomicLeft d i a (atomicVacuum d k))
      (w.eval (atomicLeft d i) (fun v => atomicLeft d j (b v))
        (atomicLeft d i c (atomicVacuum d k))) = 0 := by
  exact fockAway_inner_starts (AtomicLetters d) j _ _
    (atomicFock_vacuum_away_ne (AtomicLetters d) (atomicColumnReps d) hij a _)
    (w.creation d hij b hb K hK hw _
      (atomicFock_vacuum_away_ne (AtomicLetters d) (atomicColumnReps d) hij c _))

omit [DecidableEq V] in
theorem atomicCore_coe (w : BridgeCore (A i)) :
    ((w.eval (atomicEmbedding d i) (fun v => atomicEmbedding d j (b v)) : AtomicCStar d) :
      AtomicOperators d) = w.eval (atomicLeft d i) (fun v => atomicLeft d j (b v)) := by
  induction w with
  | single v => rfl
  | double v a u => rfl
  | flank v a w c u ih =>
    change atomicLeft d j (b v) * atomicLeft d i a *
      (↑(w.eval (atomicEmbedding d i) (fun v => atomicEmbedding d j (b v))) : AtomicOperators d) *
      atomicLeft d i c * atomicLeft d j (b u) = _
    rw [ih]
    rfl

variable {Δ : Type*} [CStarAlgebra Δ] (c : AtomicAmalgamData (Δ := Δ) d)
include hij hb hK in

theorem atomicExpectation_core_zero (w : BridgeCore (A i)) (hw : w.Centered K) :
    atomicExpectation d c i
      (w.eval (atomicEmbedding d i) (fun v => atomicEmbedding d j (b v))) = 0 := by
  apply cyclicRepresentation_injective
    (ambientFactor (atomicCStarAlgebra d) (atomicEmbedding d) i)
    (atomicVacuum d c.base) (atomicFactor_separating d c.base c.weights i)
  rw [map_zero]
  change cyclicRepresentation _ _ (factorExpectation _ _ _ _ _ _ _ _ _ _ i _) = 0
  refine (factorExpectation_rep _ _ _ _ _ _ _ _ _ _ i _).trans ?_
  apply operatorCompression_zero_of_dense _
    (cyclicOrbit (ambientFactor (atomicCStarAlgebra d) (atomicEmbedding d) i)
      (atomicVacuum d c.base))
    (cyclicOrbit_dense _ _)
  intro a z
  change inner ℂ (atomicLeft d i a (atomicVacuum d c.base))
    ((↑(w.eval (atomicEmbedding d i) (fun v => atomicEmbedding d j (b v))) : AtomicOperators d)
      (atomicLeft d i z (atomicVacuum d c.base))) = 0
  rw [atomicCore_coe]
  exact atomicCore_coefficient_zero d hij b hb K hK c.base w hw a z

include hij hb hK in
theorem atomicExpectation_sandwich_core_zero (w : BridgeCore (A i))
    (hw : w.Centered K) (a z : A i) :
    atomicExpectation d c i (atomicEmbedding d i a *
      w.eval (atomicEmbedding d i) (fun v => atomicEmbedding d j (b v)) *
      atomicEmbedding d i z) = 0 := by
  rw [atomicExpectation_mul_factor,atomicExpectation_factor_mul,
    atomicExpectation_core_zero d hij b hb K hK c w hw,mul_zero,zero_mul]

end

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

def turnCentered (i : Bool) (a : A) : Prop := (B.input false).expectation (!i) a = 0

theorem turn_matrix_centered (i j : Bool) (a : A)
    (h : i = j ∨ B.turnCentered i a) :
    B.expectation (matrixSingle (!i) j a) = 0 := by
  ext k x
  change (matrixDiagonalExpectation (B.input false).expectation (B.input false).bound
    (matrixSingle (!i) j a)) k x = 0
  rw [matrixDiagonalExpectation_apply,matrixSingle_apply]
  by_cases he : (!i) = k ∧ j = k
  · rw [ite_eq_left he]
    have hj : i ≠ j := by
      rw [he.2,← he.1]
      cases i <;> decide
    have hc := h.resolve_left hj
    change (B.input false).expectation (!i) a = 0 at hc
    rw [← he.1,hc]
    rfl
  · rw [ite_eq_right he,map_zero]
    rfl

theorem modelExpectation_hnn_word (w : HNNWord A) (a : A)
    (hw : w.Reduced B.turnCentered) :
    B.modelExpectation ((B.cornerBase a*w.eval B.cornerBase B.cornerLetter : B.Corner) : B.Model) = 0 := by
  have hc := HNNWord.matrixCore_centered B.turnCentered
    (fun z => B.expectation z = 0) B.turn_matrix_centered w hw
  have hz := atomicExpectation_sandwich_core_zero B.atoms (by decide : false ≠ true)
    (fun i => matrixSingle i (!i) (1:SequenceDiagonal))
    (fun i => B.amalgam.centered true _ (B.letter_centered i))
    (fun z => B.expectation z = 0)
    (fun z hz => B.amalgam.centered false z hz) B.amalgam w.matrixCore hc
    (matrixSingle false false a*matrixSingle false w.first 1) w.matrixFinal
  change B.modelExpectation (B.embedBase (matrixSingle false false a)*
    (↑(w.eval B.cornerBase B.cornerLetter) : B.Model)) = 0
  rw [HNNWord.eval_matrix_core]
  unfold modelExpectation embedBase embedAux bridgeLetter
  simpa only [map_mul,mul_assoc] using hz

theorem expectCorner_hnn_word (w : HNNWord A) (a : A)
    (hw : w.Reduced B.turnCentered) :
    B.expectCorner (B.cornerBase a*w.eval B.cornerBase B.cornerLetter) = 0 := by
  change (B.modelExpectation
    ((B.cornerBase a*w.eval B.cornerBase B.cornerLetter : B.Corner) : B.Model)) false false = 0
  rw [B.modelExpectation_hnn_word w a hw]
  rfl

end PeakingPairData

section
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A]
variable (e : A) (he : IsStarProjection e)

def cornerTrace (t : A →L[ℂ] ℂ) (c : ℝ) : CStarCorner e he →L[ℂ] ℂ :=
  c • t.comp (cornerSubalgebra e he).subtypeL

@[simp] theorem cornerTrace_apply (t : A →L[ℂ] ℂ) (c : ℝ) (a : CStarCorner e he) :
    cornerTrace e he t c a = c • t (a : A) := rfl

theorem cornerTrace_isState (t : A →L[ℂ] ℂ) (ht : IsState t) (c : ℝ)
    (hc : 0 ≤ c) (hn : c • t e = 1) : IsState (cornerTrace e he t c) := by
  rw [isState_iff]
  refine ⟨hn, fun a => ?_⟩
  have ha := ht.2 (a : A)
  change (c • t (star (a : A)*(a : A))).im = 0 ∧ 0 ≤ (c • t (star (a : A)*(a : A))).re
  simp only [Complex.smul_im, Complex.smul_re, smul_eq_mul, ha.1, mul_zero]
  exact ⟨trivial, mul_nonneg hc ha.2⟩

theorem cornerTrace_tracial (t : A →L[ℂ] ℂ) (c : ℝ)
    (htr : ∀ a b, t (a*b) = t (b*a)) (a b : CStarCorner e he) :
    cornerTrace e he t c (a*b) = cornerTrace e he t c (b*a) :=
  congrArg (c • ·) (htr a b)

theorem cornerTrace_faithful (t : A →L[ℂ] ℂ) (c : ℝ) (hc : c ≠ 0)
    (hf : ∀ a, t (star a*a)=0 → a=0) (a : CStarCorner e he)
    (ha : cornerTrace e he t c (star a*a)=0) : a=0 := by
  apply Subtype.ext
  apply hf
  exact (smul_eq_zero.mp ha).resolve_left hc

end

open scoped CStarAlgebra ComplexOrder

namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

abbrev modelTrace : B.Model →L[ℂ] ℂ := atomicTrace B.atoms B.amalgam

theorem modelTrace_isState : IsState B.modelTrace :=
  ⟨atomicTrace_norm B.atoms B.amalgam, atomicTrace_square B.atoms B.amalgam⟩

theorem modelTrace_base (a : CStarMatrix Bool Bool A) :
    B.modelTrace (B.embedBase a) = normalizedMatrixTrace B.trace a := by
  exact atomicTrace_factor B.atoms B.amalgam false a

def traceCorner : B.Corner →L[ℂ] ℂ :=
  cornerTrace (matrixCornerProjection B.embedBase) (matrixCornerProjection_isProjection B.embedBase)
    B.modelTrace 2

theorem traceCorner_base (a : A) : B.traceCorner (B.cornerBase a) = B.trace a := by
  change (2:ℝ) • B.modelTrace (B.embedBase (matrixSingle false false a)) = B.trace a
  rw [B.modelTrace_base,normalizedMatrixTrace_single]
  simp only [Fintype.card_bool, Nat.cast_ofNat, smul_smul]
  norm_num

theorem traceCorner_isState : IsState B.traceCorner := by
  apply cornerTrace_isState _ _ B.modelTrace B.modelTrace_isState 2 (by norm_num)
  change (2:ℝ) • B.modelTrace (B.embedBase (matrixSingle false false (1:A))) = 1
  rw [B.modelTrace_base,normalizedMatrixTrace_single,B.normalized]
  norm_num

theorem traceCorner_tracial (a b : B.Corner) : B.traceCorner (a*b) = B.traceCorner (b*a) :=
  cornerTrace_tracial _ _ B.modelTrace 2 (atomicTrace_mul B.atoms B.amalgam) a b

theorem traceCorner_faithful (a : B.Corner) (ha : B.traceCorner (star a*a) = 0) : a = 0 :=
  cornerTrace_faithful _ _ B.modelTrace 2 (by norm_num)
    (atomicTrace_faithful B.atoms B.amalgam) a ha

theorem traceCorner_strict (a : B.Corner) (ha : a ≠ 0) :
    0 < (B.traceCorner (star a*a)).re := by
  apply lt_of_le_of_ne (B.traceCorner_isState.2 a).2
  intro hz
  apply ha
  apply B.traceCorner_faithful
  apply Complex.ext
  · exact hz.symm
  · exact (B.traceCorner_isState.2 a).1

theorem traceCorner_faithfulTracial : IsFaithfulTracialState B.traceCorner :=
  ⟨B.traceCorner_isState,B.traceCorner_tracial,B.traceCorner_strict⟩

end PeakingPairData

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
  (E : C →L[ℂ] CStarMatrix Bool Bool A) (τ : A →ₚ[ℂ] ℂ) (t : C →L[ℂ] ℂ)

theorem matrixCorner_trace_expectation
    (hleft : ∀ a x, E (φ a*x) = a*E x)
    (hright : ∀ x a, E (x*φ a) = E x*a)
    (htrace : ∀ x, normalizedMatrixTrace τ (E x) = t x) (x : MatrixHNNCorner φ) :
    τ (matrixCornerExpectation φ E x) =
      cornerTrace (matrixCornerProjection φ) (matrixCornerProjection_isProjection φ) t 2 x := by
  have ht := htrace (x:C)
  rw [matrixCornerExpectation_supported φ E hleft hright,normalizedMatrixTrace_single] at ht
  change τ (matrixCornerExpectation φ E x) = (2:ℝ) • t (x:C)
  rw [← ht]
  simp only [Fintype.card_bool,Nat.cast_ofNat,smul_smul]
  norm_num

end

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem traceCorner_expectation (x : B.Corner) :
    B.trace (B.expectCorner x) = B.traceCorner x :=
  matrixCorner_trace_expectation B.embedBase B.modelExpectation B.trace B.modelTrace
    (atomicExpectation_factor_mul B.atoms B.amalgam false)
    (atomicExpectation_mul_factor B.atoms B.amalgam false)
    (atomicExpectation_trace B.atoms B.amalgam false) x

theorem traceCorner_hnn_word (w : HNNWord A) (a : A)
    (hw : w.Reduced B.turnCentered) :
    B.traceCorner (B.cornerBase a*w.eval B.cornerBase B.cornerLetter) = 0 := by
  rw [← B.traceCorner_expectation,B.expectCorner_hnn_word w a hw,map_zero]

end PeakingPairData

section
variable {A C D : Type*} [Ring A] [Ring C] [Ring D]
  (φ : A →+* C) (δ : Bool → D →+* A) (v : Bool → C)

theorem hnn_reverse_conjugacy (hleft : v false*v true = 1)
    (hconj : ∀ d, v true*φ (δ false d)*v false = φ (δ true d))
    (i : Bool) (d : D) : v i*φ (δ (!i) d)*v (!i) = φ (δ i d) := by
  cases i
  · change v false*φ (δ true d)*v true = φ (δ false d)
    rw [← hconj d]
    calc
      _ = (v false*v true)*φ (δ false d)*(v false*v true) := by simp only [mul_assoc]
      _ = _ := by rw [hleft,one_mul,mul_one]
  · exact hconj d

theorem hnn_turn_split (E : Bool → A → D)
    (hconj : ∀ i d, v i*φ (δ (!i) d)*v (!i) = φ (δ i d)) (i : Bool) (a : A) :
    v i*φ a*v (!i) = v i*φ (a-δ (!i) (E (!i) a))*v (!i) + φ (δ i (E (!i) a)) := by
  rw [map_sub,mul_sub,sub_mul,hconj,sub_add_cancel]
end

open scoped CStarAlgebra
section
variable {A D Z : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra Z]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z) (ψ : CStarMatrix Bool Bool D →⋆ₐ[ℂ] Z)
  (δ : Bool → D →⋆ₐ[ℂ] A)
  (hd : ∀ x, φ (matrixDiagonalHom δ x) =
    ψ (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D) x))

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in

theorem matrixCornerLetter_diagonal (i : Bool) (d : D) :
    matrixCornerLetter φ ψ (matrixDiagonal_units φ ψ δ hd) i *
      matrixCornerBase φ (δ (!i) d) *
      matrixCornerLetter φ ψ (matrixDiagonal_units φ ψ δ hd) (!i) =
        matrixCornerBase φ (δ i d) :=
  hnn_reverse_conjugacy (matrixCornerBase φ).toRingHom (fun i => (δ i).toRingHom)
    (matrixCornerLetter φ ψ (matrixDiagonal_units φ ψ δ hd))
    (matrixStable_star_mul φ ψ (matrixDiagonal_units φ ψ δ hd))
    (matrixStable_conjugates φ ψ δ hd) i d

end

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem cornerLetter_diagonal (i : Bool) (a : SequenceDiagonal) :
    B.cornerLetter i*B.cornerBase (B.diagonal (!i) a)*B.cornerLetter (!i) =
      B.cornerBase (B.diagonal i a) :=
  matrixCornerLetter_diagonal B.embedBase B.embedAux B.diagonal B.model_diagonal_agree i a

def turnCenter (i : Bool) (a : A) : A :=
  a-B.diagonal (!i) ((B.input false).expectation (!i) a)

def turnRemainder (i : Bool) (a : A) : A :=
  B.diagonal i ((B.input false).expectation (!i) a)

theorem turnCenter_centered (i : Bool) (a : A) :
    (B.input false).expectation (!i) (B.turnCenter i a) = 0 := by
  unfold turnCenter
  rw [map_sub,(B.input false).fix,sub_self]

theorem cornerLetter_turn (i : Bool) (a : A) :
    B.cornerLetter i*B.cornerBase a*B.cornerLetter (!i) =
      B.cornerLetter i*B.cornerBase (B.turnCenter i a)*B.cornerLetter (!i) +
        B.cornerBase (B.turnRemainder i a) :=
  hnn_turn_split B.cornerBase.toRingHom (fun i => (B.diagonal i).toRingHom)
    B.cornerLetter (fun i => (B.input false).expectation i) B.cornerLetter_diagonal i a

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem corner_restriction {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) (hw : ∀ i, star (w i) = w (!i))
    (hr : ∀ i a, w i*ψ a*w (!i) = w i*ψ (B.turnCenter i a)*w (!i) +
      ψ (B.turnRemainder i a))
    (g : C →ₚ[ℂ] ℂ) (hg : ∀ c : C, g (star c*c) = 0 → c = 0)
    (hbase : ∀ a, g (ψ a) = B.trace a)
    (hred : ∀ (u : HNNWord A) a, u.Reduced B.turnCentered →
      g (ψ a*u.eval ψ w) = 0) :
    ∃ F : B.Corner →⋆ₐ[ℂ] C, Function.Injective F ∧
      (∀ a, F (B.cornerBase a) = ψ a) ∧ (∀ i, F (B.cornerLetter i) = w i) ∧
      (∀ b, g (F b) = B.traceCorner b) ∧ F.range = hnnGenerated ψ w := by
  apply exists_hnnRestriction B.cornerBase ψ B.cornerLetter w B.cornerLetter_star hw
    B.turnCentered B.turnCenter B.turnRemainder B.turnCenter_centered B.cornerLetter_turn hr
    (positiveOfSquares B.traceCorner B.traceCorner_isState.2) g
  · intro a
    exact (B.traceCorner_base a).trans (hbase a).symm
  · intro u a hu
    exact (B.traceCorner_hnn_word u a hu).trans (hred u a hu).symm
  · exact B.traceCorner_faithful
  · exact hg
  · exact B.corner_generated

theorem corner_restriction_expectation {C D : Type*} [CStarAlgebra C] [CStarAlgebra D]
    (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) (ι : A →⋆ₐ[ℂ] D)
    (F : B.Corner →⋆ₐ[ℂ] C) (hbase : ∀ a, F (B.cornerBase a) = ψ a)
    (hletter : ∀ i, F (B.cornerLetter i) = w i)
    (G : C →L[ℂ] D) (hG : ∀ a, G (ψ a) = ι a)
    (hGr : ∀ (u : HNNWord A) a, u.Reduced B.turnCentered →
      G (ψ a*u.eval ψ w) = 0) (b : B.Corner) :
    G (F b) = ι (B.expectCorner b) :=
  hnn_expectation_intertwines B.cornerBase ψ ι B.cornerLetter w F hbase hletter
    B.cornerLetter_star B.turnCentered B.turnCenter B.turnRemainder B.turnCenter_centered
    B.cornerLetter_turn B.expectCorner G B.expectCorner_base hG B.expectCorner_hnn_word hGr
    B.corner_generated b

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [instA : CStarAlgebra A] [orderA : PartialOrder A]
  [starOrderA : StarOrderedRing A] (B : PeakingPairData A)

def HNNAlgebra : Type := B.Corner
instance hnnCStar : CStarAlgebra B.HNNAlgebra :=
  cornerCStarAlgebra (A := B.Model) (matrixCornerProjection B.embedBase)
    (matrixCornerProjection_isProjection B.embedBase)
instance hnnOrder : PartialOrder B.HNNAlgebra :=
  cornerPartialOrder (A := B.Model) (matrixCornerProjection B.embedBase)
    (matrixCornerProjection_isProjection B.embedBase)
instance hnnStarOrder : StarOrderedRing B.HNNAlgebra :=
  cornerStarOrderedRing (A := B.Model) (matrixCornerProjection B.embedBase)
    (matrixCornerProjection_isProjection B.embedBase)

def hnnBase : A →⋆ₐ[ℂ] B.HNNAlgebra := B.cornerBase
def hnnLetter : Bool → B.HNNAlgebra := B.cornerLetter
def hnnTrace : B.HNNAlgebra →L[ℂ] ℂ := B.traceCorner
def hnnExpectation : B.HNNAlgebra →L[ℂ] A := B.expectCorner

theorem hnnBase_injective : Function.Injective B.hnnBase := B.cornerBase_injective
theorem hnnLetter_star (i : Bool) : star (B.hnnLetter i) = B.hnnLetter (!i) :=
  B.cornerLetter_star i
theorem hnnLetter_turn (i : Bool) (a : A) :
    B.hnnLetter i*B.hnnBase a*B.hnnLetter (!i) =
      B.hnnLetter i*B.hnnBase (B.turnCenter i a)*B.hnnLetter (!i) + B.hnnBase (B.turnRemainder i a) :=
  B.cornerLetter_turn i a
theorem hnn_generated :
    Dense (StarAlgebra.adjoin ℂ (Set.range B.hnnBase ∪ Set.range B.hnnLetter) : Set B.HNNAlgebra) :=
  B.corner_generated
theorem hnnTrace_isState : IsState B.hnnTrace := B.traceCorner_isState
theorem hnnTrace_base (a : A) : B.hnnTrace (B.hnnBase a) = B.trace a := B.traceCorner_base a
theorem hnnTrace_faithful (a : B.HNNAlgebra) (ha : B.hnnTrace (star a*a) = 0) : a = 0 :=
  B.traceCorner_faithful a ha
theorem hnnTrace_tracial (a b : B.HNNAlgebra) : B.hnnTrace (a*b) = B.hnnTrace (b*a) :=
  B.traceCorner_tracial a b
theorem hnnExpectation_base (a : A) : B.hnnExpectation (B.hnnBase a) = a := B.expectCorner_base a
theorem hnnExpectation_word (u : HNNWord A) (a : A) (hu : u.Reduced B.turnCentered) :
    B.hnnExpectation (B.hnnBase a*u.eval B.hnnBase B.hnnLetter) = 0 := B.expectCorner_hnn_word u a hu
theorem hnnTrace_expectation (a : B.HNNAlgebra) : B.trace (B.hnnExpectation a) = B.hnnTrace a :=
  B.traceCorner_expectation a

end PeakingPairData

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (e : A) (he : IsStarProjection e)

def cornerRestrictState (f : A →L[ℂ] ℂ) : CStarCorner e he →L[ℂ] ℂ :=
  f.comp (cornerSubalgebra e he).subtypeL

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem cornerRestrictState_apply (f : A →L[ℂ] ℂ) (a : CStarCorner e he) :
    cornerRestrictState e he f a = f (a : A) := rfl

omit [PartialOrder A] [StarOrderedRing A] in

theorem cornerRestrictState_isState (f : A →L[ℂ] ℂ) (hf : IsState f) (hfe : f e = 1) :
    IsState (cornerRestrictState e he f) := by
  rw [isState_iff]
  exact ⟨hfe,fun a => hf.2 (a:A)⟩

theorem cornerLift_restrict (f : A →L[ℂ] ℂ) (hf : IsState f) (hfe : f e = 1) :
    cornerLiftState e he (cornerRestrictState e he f) = f := by
  ext a
  exact state_compression f hf e (he.norm_le e) he.isSelfAdjoint hfe a

theorem cornerLiftState_isPureState (g : CStarCorner e he →L[ℂ] ℂ) (hg : IsPureState g) :
    IsPureState (cornerLiftState e he g) := by
  rw [IsPureState,mem_extremePoints]
  refine ⟨cornerLiftState_isState e he g hg.1,?_⟩
  intro f hf h hh hseg
  obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
  have hcomp : cornerCompression e he e = 1 := by
    apply Subtype.ext
    change e*e*e=e
    rw [he.isIdempotentElem.eq,he.isIdempotentElem.eq]
  have hface := state_projection_face f h hf hh e he a b ha hb hab (by
    rw [heq]
    change g (cornerCompression e he e) = 1
    rw [hcomp,((isState_iff g).mp hg.1).1])
  have heqr : a • cornerRestrictState e he f + b • cornerRestrictState e he h = g := by
    ext x
    have hh := congrArg (fun k : A →L[ℂ] ℂ => k (x:A)) heq
    simpa only [map_add,smul_apply, add_apply,cornerRestrictState_apply,
      cornerLiftState_apply,cornerCompression_corner] using hh
  have hbase := (mem_extremePoints.mp hg).2 _
    (cornerRestrictState_isState e he f hf hface.1) _
    (cornerRestrictState_isState e he h hh hface.2) ⟨a,b,ha,hb,hab,heqr⟩
  constructor
  · rw [← cornerLift_restrict e he f hf hface.1,hbase.1]
  · rw [← cornerLift_restrict e he h hh hface.2,hbase.2]

theorem pureState_equivalent_of_conjugate (f g : A →L[ℂ] ℂ)
    (hf : IsPureState f) (hg : IsPureState g) (u : unitary A)
    (hc : ∀ a, g a = f (star (u:A)*a*(u:A))) :
    UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg) := by
  let F := positiveOfSquares f hf.1.2
  let G := positiveOfSquares g hg.1.2
  let ξ := F.gnsStarAlgHom u (gnsVector F)
  have hfc (a : A) : ⟪ξ,F.gnsStarAlgHom a ξ⟫_ℂ = g a := by
    rw [hc]
    change ⟪F.gnsStarAlgHom u (gnsVector F),
      F.gnsStarAlgHom a (F.gnsStarAlgHom u (gnsVector F))⟫_ℂ = f (star (u:A)*a*(u:A))
    change _ = F (star (u:A)*a*(u:A))
    rw [← gnsVector_coefficient F]
    simp only [map_mul,map_star,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  have hξ : ξ ≠ 0 := by
    intro hz
    have hh := hfc 1
    rw [hz,inner_zero_left,((isState_iff g).mp hg.1).1] at hh
    exact zero_ne_one hh
  exact irreducible_equivalent_of_coefficients (pureGNS f hf)
    (pure_gns_irreducible f hf.1 hf) (pureGNS g hg)
    (pure_gns_irreducible g hg.1 hg) ξ (gnsVector G) hξ
    (norm_ne_zero_iff.mp ((gnsVector_norm_eq_one G ((isState_iff g).mp hg.1).1).trans_ne one_ne_zero))
    (fun a => (hfc a).trans (gnsVector_coefficient G a).symm)

end

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem Peaks.join_extensions {p q : ℕ → A} {f g : A →L[ℂ] ℂ}
    (hp : Peaks p f) (hq : Peaks q g) (φ : A →⋆ₐ[ℂ] C) (u : unitary C)
    (hconj : ∀ n, (u:C)*φ (p n)*star (u:C) = φ (q n))
    (hu : StateExtensionUnique φ g)
    (F G : C →L[ℂ] ℂ) (hF : IsPureState F) (hG : IsPureState G)
    (hrF : restrictState φ F = f) (hrG : restrictState φ G = g) :
    UnitarilyEquivalent (pureGNS F hF) (pureGNS G hG) := by
  let H := restrictState (Unitary.conjStarAlgAut ℂ C u).symm.toStarAlgHom F
  have hH : IsState H := isState_restrict _ _ hF.1
  have hres : restrictState φ H = g := by
    apply hq.2.2.2.2 _ (isState_restrict φ H hH)
    intro n
    change F (star (u:C)*φ (q n)*(u:C)) = 1
    rw [← hconj]
    have hh : star (u:C)*((u:C)*φ (p n)*star (u:C))*(u:C) = φ (p n) := by
      calc
        _ = (star (u:C)*(u:C))*φ (p n)*(star (u:C)*(u:C)) := by simp only [mul_assoc]
        _ = _ := by rw [u.property.1,one_mul,mul_one]
    rw [hh]
    change restrictState φ F (p n) = 1
    rw [hrF]
    exact hp.2.2.2.1 n
  have he := hu H G hH hG.1 hres hrG
  apply pureState_equivalent_of_conjugate F G hF hG u
  intro a
  exact (congrArg (fun k : C →L[ℂ] ℂ => k a) he).symm

end

section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def PureStateEquivalent (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (g : A →L[ℂ] ℂ) (hg : IsPureState g) : Prop :=
  UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg)

variable {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
theorem Peaks.join_named {p q : ℕ → A} {f g : A →L[ℂ] ℂ}
    (hp : Peaks p f) (hq : Peaks q g) (φ : A →⋆ₐ[ℂ] C) (u : unitary C)
    (hconj : ∀ n, (u:C)*φ (p n)*star (u:C) = φ (q n))
    (hu : StateExtensionUnique φ g)
    (F G : C →L[ℂ] ℂ) (hF : IsPureState F) (hG : IsPureState G)
    (hrF : restrictState φ F = f) (hrG : restrictState φ G = g) :
    PureStateEquivalent F hF G hG :=
  hp.join_extensions hq φ u hconj hu F G hF hG hrF hrG
end

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C]
  {ι : Type*} {l : Filter ι} [l.NeBot]

omit [PartialOrder A] [StarOrderedRing A] in

theorem no_common_irrep_of_state_decay (φ : A →⋆ₐ[ℂ] C) (f g : A →L[ℂ] ℂ)
    (S : Set C) (hd : Dense (Submodule.span ℂ S : Set C)) (x y : ι → A)
    (hx : ∀ i, IsSelfAdjoint (x i)) (hxn : ∀ i, ‖x i‖ ≤ 1) (hyn : ∀ i, ‖y i‖ ≤ 1)
    (hxv : ∀ i, f (x i) = 1) (hyv : ∀ i, g (y i) = 1)
    (hdec : ∀ a ∈ S, Tendsto (fun i => φ (x i)*a*φ (y i)) l (𝓝 0))
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hcξ : ∀ a, ⟪ξ,π (φ a) ξ⟫_ℂ = f a)
    (hcη : ∀ a, ⟪η,π (φ a) η⟫_ℂ = g a) : False := by
  apply no_common_irrep_of_dense_decay π hπ ξ η
    (norm_ne_zero_iff.mp (hξ.trans_ne one_ne_zero))
    (norm_ne_zero_iff.mp (hη.trans_ne one_ne_zero)) S hd
    (fun i => φ (x i)) (fun i => φ (y i)) (fun i => (hx i).map φ) ?_ ?_ hdec
  · intro i
    exact representation_fix_of_coefficient_one π ξ hξ _
      ((NonUnitalStarAlgHom.norm_apply_le φ _).trans (hxn i)) ((hcξ _).trans (hxv i))
  · intro i
    exact representation_fix_of_coefficient_one π η hη _
      ((NonUnitalStarAlgHom.norm_apply_le φ _).trans (hyn i)) ((hcη _).trans (hyv i))

omit [PartialOrder A] [StarOrderedRing A] [l.NeBot] in

theorem map_cross_decay (φ : A →⋆ₐ[ℂ] C) (x y : ι → A) (a : A)
    (ht : Tendsto (fun i => x i*a*y i) l (𝓝 0)) :
    Tendsto (fun i => φ (x i)*φ a*φ (y i)) l (𝓝 0) := by
  simpa only [Function.comp_def,map_zero,map_mul] using ((map_continuous φ).tendsto 0).comp ht

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C]
  {ι κ : Type*} [Preorder ι] [Preorder κ]
  [IsDirectedOrder ι] [IsDirectedOrder κ] [Nonempty ι] [Nonempty κ]

theorem bridge_cross_decay (φ : A →⋆ₐ[ℂ] C) (v : Bool → C) (K : A → Prop)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (x : ι → A) (y : κ → A) (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ 1)
    (hy : ∀ j, 0 ≤ y j) (hyn : ∀ j, ‖y j‖ ≤ 1) (hym : Antitone y)
    (hexc : ∀ a, Tendsto (fun i => x i*(a-f a • (1:A))*x i) atTop (𝓝 0))
    (hey : ∀ a, Tendsto (fun j => y j*(a-g a • (1:A))*y j) atTop (𝓝 0))
    (hne : ¬ UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg))
    (hword : ∀ w : BridgeCore A, w.Centered K → ∀ a c : A,
      Tendsto (fun k : ι × κ => φ (x k.1)*φ a*w.eval φ v*φ c*φ (y k.2))
        atTop (𝓝 0)) :
    ∀ a ∈ bridgeWordSet φ v K,
      Tendsto (fun k : ι × κ => φ (x k.1)*a*φ (y k.2)) atTop (𝓝 0) := by
  let : (atTop : Filter (ι × κ)).NeBot := by
    rw [← prod_atTop_atTop_eq]
    infer_instance
  intro a ha
  rcases ha with (⟨a,rfl⟩ | ⟨w,a,c,hw,rfl⟩)
  · exact map_cross_decay φ _ _ a
      (state_cross_excision f g hf hg x y hx hxn hy hyn hym hexc hey hne a)
  · simpa only [mul_assoc] using hword w hw a c

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {B : PeakingPairData A} {ι κ : Type*} [Preorder ι] [Preorder κ]
  [IsDirectedOrder ι] [IsDirectedOrder κ] [Nonempty ι] [Nonempty κ]
  (X : B.Endpoint ι) (Y : B.Endpoint κ)

theorem Endpoint.cross_decay (hs : B.Separated)
    (hex : ∀ i, X.tag = some i → Y.tag ≠ some (!i))
    (hne : ¬ UnitarilyEquivalent (pureGNS X.state X.pure) (pureGNS Y.state Y.pure)) :
    ∀ a ∈ bridgeWordSet B.embedBase B.modelLetter (fun a => B.expectation a = 0),
      Tendsto (fun k : ι × κ => B.embedBase (X.net k.1)*a*B.embedBase (Y.net k.2))
        atTop (𝓝 0) :=
  bridge_cross_decay B.embedBase B.modelLetter (fun a => B.expectation a = 0)
    X.state Y.state X.pure Y.pure X.net Y.net X.positive X.contractive
    Y.positive Y.contractive Y.antitone X.excision Y.excision hne
    (X.model_word_decay Y hs hex)

theorem Endpoint.disjoint_matrix_irrep (hs : B.Separated)
    (hex : ∀ i, X.tag = some i → Y.tag ≠ some (!i))
    (hne : ¬ UnitarilyEquivalent (pureGNS X.state X.pure) (pureGNS Y.state Y.pure))
    (hxval : ∀ k, X.state (X.net k) = 1) (hyval : ∀ k, Y.state (Y.net k) = 1)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : B.Model →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hcξ : ∀ a, ⟪ξ,π (B.embedBase a) ξ⟫_ℂ = X.state a)
    (hcη : ∀ a, ⟪η,π (B.embedBase a) η⟫_ℂ = Y.state a) : False := by
  let : (atTop : Filter (ι × κ)).NeBot := by
    rw [← prod_atTop_atTop_eq]
    infer_instance
  exact no_common_irrep_of_state_decay B.embedBase X.state Y.state
    (bridgeWordSet B.embedBase B.modelLetter (fun a => B.expectation a = 0)) B.model_words_dense
    (fun k : ι × κ => X.net k.1) (fun k : ι × κ => Y.net k.2)
    (fun k => IsSelfAdjoint.of_nonneg (X.positive k.1))
    (fun k => X.contractive k.1) (fun k => Y.contractive k.2)
    (fun k => hxval k.1) (fun k => hyval k.2)
    (X.cross_decay Y hs hex hne) π hπ ξ η hξ hη hcξ hcη

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem exists_endpoint_representative (hs : B.Separated)
    (f : CStarMatrix Bool Bool A →L[ℂ] ℂ) (hf : IsPureState f)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ p : CStarMatrix Bool Bool A,
      IsStarProjection p ∧ pureGNS f hf p ≠ 0 ∧ (B.matrixTrace p).re < ε) :
    ∃ (ι : Type) (_po : Preorder ι) (_dir : IsDirectedOrder ι) (_ne : Nonempty ι)
      (X : B.Endpoint ι),
      UnitarilyEquivalent (pureGNS X.state X.pure) (pureGNS f hf) ∧
        ∀ k, X.state (X.net k) = 1 := by
  classical
  by_cases he : ∃ i, UnitarilyEquivalent (pureGNS (B.matrixState i) (B.matrixPure i))
      (pureGNS f hf)
  · obtain ⟨i,hi⟩ := he
    refine ⟨ℕ,inferInstance,inferInstance,inferInstance,B.peakEndpoint hs i,hi,?_⟩
    exact (B.matrixPeaks i).2.2.2.1
  · have hne : ∀ i, ¬ UnitarilyEquivalent (pureGNS f hf)
        (pureGNS (B.matrixState i) (B.matrixPure i)) := by
      intro i hi
      exact he ⟨i,UnitarilyEquivalent.symm hi⟩
    exact ⟨B.pureIndex f hf,inferInstance,inferInstance,inferInstance,
      B.otherEndpoint f hf hsmall hne,UnitarilyEquivalent.refl _,
      B.otherEndpoint_value_one f hf hsmall hne⟩

end PeakingPairData

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem equivalent_pure_coefficient_vector (φ : A →⋆ₐ[ℂ] C)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (he : UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg))
    (π : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hc : ∀ a, ⟪ξ,π (φ a) ξ⟫_ℂ = f a) :
    ∃ η : H, ‖η‖ = 1 ∧ ∀ a, ⟪η,π (φ a) η⟫_ℂ = g a := by
  obtain ⟨u,hu⟩ := pureState_equivalent_conjugate f g hf hg he
  let ψ := π.comp φ.toNonUnitalStarAlgHom
  let η := π (φ (u:A)) ξ
  have hn : (‖η‖ : ℂ)^2 = 1 := by
    calc
      _ = vectorFunctional ψ ξ (star (u:A)*(u:A)) :=
        (vectorFunctional_square ψ ξ (u:A)).symm
      _ = f (star (u:A)*(u:A)) := hc _
      _ = 1 := by rw [u.property.1,((isState_iff f).mp hf.1).1]
  refine ⟨η,?_,?_⟩
  · have hn' := congrArg Complex.re hn
    simp only [← Complex.ofReal_pow,Complex.ofReal_re,Complex.one_re] at hn'
    nlinarith [norm_nonneg η]
  · intro a
    change ⟪π (φ (u:A)) ξ,π (φ a) (π (φ (u:A)) ξ)⟫_ℂ = g a
    calc
      _ = ⟪ξ,π (φ (star (u:A)*a*(u:A))) ξ⟫_ℂ := by
        simp only [map_mul,map_star,mul_apply_eq_comp,
          ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      _ = f (star (u:A)*a*(u:A)) := hc _
      _ = g a := (congrArg (fun k : A →L[ℂ] ℂ => k a) hu).symm

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace
theorem pureGNS_equivalent_of_state_eq {D : Type*} [CStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D]
    (f g : D →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) (h : f = g) :
    UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg) := by
  subst g
  exact UnitarilyEquivalent.refl _

namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem matrix_no_unintended_join (hs : B.Separated)
    (f g : CStarMatrix Bool Bool A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (hsmallf : ∀ ε : ℝ, 0 < ε → ∃ p : CStarMatrix Bool Bool A,
      IsStarProjection p ∧ pureGNS f hf p ≠ 0 ∧ (B.matrixTrace p).re < ε)
    (hsmallg : ∀ ε : ℝ, 0 < ε → ∃ p : CStarMatrix Bool Bool A,
      IsStarProjection p ∧ pureGNS g hg p ≠ 0 ∧ (B.matrixTrace p).re < ε)
    (hne : ¬ UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg))
    (hex : ∀ i, ¬ (UnitarilyEquivalent (pureGNS f hf)
        (pureGNS (B.matrixState i) (B.matrixPure i)) ∧
      UnitarilyEquivalent (pureGNS g hg)
        (pureGNS (B.matrixState (!i)) (B.matrixPure (!i)))))
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : B.Model →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ η : H)
    (hcξ : ∀ a, ⟪ξ,π (B.embedBase a) ξ⟫_ℂ = f a)
    (hcη : ∀ a, ⟪η,π (B.embedBase a) η⟫_ℂ = g a) : False := by
  obtain ⟨ι,poι,dι,nι,X,hX,hvalX⟩ := B.exists_endpoint_representative hs f hf hsmallf
  let : Preorder ι := poι
  let : IsDirectedOrder ι := dι
  let : Nonempty ι := nι
  obtain ⟨κ,poκ,dκ,nκ,Y,hY,hvalY⟩ := B.exists_endpoint_representative hs g hg hsmallg
  let : Preorder κ := poκ
  let : IsDirectedOrder κ := dκ
  let : Nonempty κ := nκ
  have hnXY : ¬ UnitarilyEquivalent (pureGNS X.state X.pure) (pureGNS Y.state Y.pure) := by
    intro h
    exact hne (hX.symm.trans (h.trans hY))
  have heXY : ∀ i, X.tag = some i → Y.tag ≠ some (!i) := by
    intro i hi hj
    have hXi : UnitarilyEquivalent (pureGNS X.state X.pure)
        (pureGNS (B.matrixState i) (B.matrixPure i)) := by
      exact pureGNS_equivalent_of_state_eq _ _ _ _ (X.matchedState i hi)
    have hYj : UnitarilyEquivalent (pureGNS Y.state Y.pure)
        (pureGNS (B.matrixState (!i)) (B.matrixPure (!i))) := by
      exact pureGNS_equivalent_of_state_eq _ _ _ _ (Y.matchedState (!i) hj)
    exact hex i ⟨hX.symm.trans hXi,hY.symm.trans hYj⟩
  obtain ⟨ξ',hξ',hcξ'⟩ := equivalent_pure_coefficient_vector B.embedBase f X.state hf X.pure
    hX.symm π ξ hcξ
  obtain ⟨η',hη',hcη'⟩ := equivalent_pure_coefficient_vector B.embedBase g Y.state hg Y.pure
    hY.symm π η hcη
  exact X.disjoint_matrix_irrep Y hs heXY hnXY hvalX hvalY π hπ ξ' η' hξ' hη' hcξ' hcη'

end PeakingPairData

open scoped CStarAlgebra ComplexOrder
section
variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

def cornerUnitary (u : unitary (CStarCorner e he)) : unitary A := by
  let x : CStarCorner e he := u
  have hx : star (x:A)*(x:A)=e := congrArg (fun c : CStarCorner e he => (c:A)) u.property.1
  have hy : (x:A)*star (x:A)=e := congrArg (fun c : CStarCorner e he => (c:A)) u.property.2
  have hs : e*star (x:A)=star (x:A) ∧ star (x:A)*e=star (x:A) := (star x).property
  refine ⟨(x:A)+(1-e),?_,?_⟩
  · simp only [star_add,star_sub,star_one,he.isSelfAdjoint.star_eq,
      add_mul,mul_add,sub_mul,mul_sub,one_mul,mul_one,hx,x.property.1,hs.2,he.isIdempotentElem.eq]
    abel
  · simp only [star_add,star_sub,star_one,he.isSelfAdjoint.star_eq,
      add_mul,mul_add,sub_mul,mul_sub,one_mul,mul_one,hy,x.property.2,hs.1,he.isIdempotentElem.eq]
    abel

@[simp] theorem cornerUnitary_apply (u : unitary (CStarCorner e he)) :
    (cornerUnitary e he u : A) = ((u : CStarCorner e he):A)+(1-e) := rfl

theorem cornerCompression_conjugate (u : unitary (CStarCorner e he)) (a : A) :
    cornerCompression e he (star (cornerUnitary e he u : A)*a*(cornerUnitary e he u : A)) =
      star (u:CStarCorner e he)*cornerCompression e he a*(u:CStarCorner e he) := by
  let x : CStarCorner e he := u
  have hs : star (x:A)*e = star (x:A) := (star x).property.2
  have hl : e*star (cornerUnitary e he u : A) = star (x:A) := by
    rw [cornerUnitary_apply]
    simp only [star_add,star_sub,star_one,he.isSelfAdjoint.star_eq,mul_add,mul_sub,
      mul_one,he.isIdempotentElem.eq,sub_self,add_zero]
    exact (star x).property.1
  have hr : (cornerUnitary e he u : A)*e = (x:A) := by
    rw [cornerUnitary_apply]
    simp only [add_mul,sub_mul,one_mul,he.isIdempotentElem.eq,sub_self,add_zero]
    exact x.property.2
  apply Subtype.ext
  change e*(star (cornerUnitary e he u : A)*a*(cornerUnitary e he u : A))*e =
    star (x:A)*(e*a*e)*(x:A)
  calc
    _ = (e*star (cornerUnitary e he u : A))*a*((cornerUnitary e he u : A)*e) := by
      simp only [mul_assoc]
    _ = star (x:A)*a*(x:A) := by rw [hl,hr]
    _ = _ := by
      symm
      calc
        _ = (star (x:A)*e)*a*(e*(x:A)) := by simp only [mul_assoc]
        _ = _ := by rw [hs,x.property.1]

variable [PartialOrder A] [StarOrderedRing A]

theorem cornerLift_equivalence (f g : CStarCorner e he →L[ℂ] ℂ)
    (hf : IsPureState f) (hg : IsPureState g)
    (hu : UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg)) :
    UnitarilyEquivalent
      (pureGNS (cornerLiftState e he f) (cornerLiftState_isPureState e he f hf))
      (pureGNS (cornerLiftState e he g) (cornerLiftState_isPureState e he g hg)) := by
  obtain ⟨u,hu⟩ := pureState_equivalent_conjugate f g hf hg hu
  apply pureState_equivalent_of_conjugate _ _
    (cornerLiftState_isPureState e he f hf) (cornerLiftState_isPureState e he g hg)
    (cornerUnitary e he u)
  intro a
  change g (cornerCompression e he a) = f (cornerCompression e he _)
  rw [cornerCompression_conjugate]
  exact congrArg (fun k : CStarCorner e he →L[ℂ] ℂ => k (cornerCompression e he a)) hu

end

open scoped CStarAlgebra ComplexOrder InnerProductSpace
section
universe u v
variable {A : Type u} {C : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem corner_extensions_inequivalent_of_matrix_no_common
    (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C) (f g : A →L[ℂ] ℂ)
    (hno : ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      ∀ (π : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)), IsIrreducible π →
      ∀ ξ η : H, ‖ξ‖ = 1 → ‖η‖ = 1 →
      (∀ a, ⟪ξ,π (φ a) ξ⟫_ℂ = matrixState f false a) →
      (∀ a, ⟪η,π (φ a) η⟫_ℂ = matrixState g false a) → False)
    (F G : MatrixHNNCorner φ →L[ℂ] ℂ) (hF : IsPureState F) (hG : IsPureState G)
    (hrF : restrictState (matrixCornerBase φ) F = f)
    (hrG : restrictState (matrixCornerBase φ) G = g) :
    ¬ UnitarilyEquivalent (pureGNS F hF) (pureGNS G hG) := by
  intro h
  let e := matrixCornerProjection φ
  let he := matrixCornerProjection_isProjection φ
  have hr (K : MatrixHNNCorner φ →L[ℂ] ℂ) (k : A →L[ℂ] ℂ)
      (hk : restrictState (matrixCornerBase φ) K = k) :
      restrictState φ (cornerLiftState e he K) = matrixState k false := by
    ext M
    change K (cornerCompression e he (φ M)) = k (M false false)
    rw [matrixCorner_compression]
    exact congrArg (fun t : A →L[ℂ] ℂ => t (M false false)) hk
  exact pure_extensions_inequivalent_of_no_common φ (matrixState f false) (matrixState g false)
    hno _ _ (cornerLiftState_isPureState e he F hF) (cornerLiftState_isPureState e he G hG)
    (hr F f hrF) (hr G g hrG) (cornerLift_equivalence e he F G hF hG h)

end

open scoped CStarAlgebra ComplexOrder InnerProductSpace
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A : Type} [instA : CStarAlgebra A] [orderA : PartialOrder A]
  [starOrderA : StarOrderedRing A] (B : PeakingPairData A)

def hnnUnitary : unitary B.HNNAlgebra := B.stableUnitary

theorem hnnUnitary_conjugates (n : ℕ) :
    (B.hnnUnitary:B.HNNAlgebra)*B.hnnBase (B.peak false n)*star (B.hnnUnitary:B.HNNAlgebra) =
      B.hnnBase (B.peak true n) := B.stable_conjugates_peak n

theorem hnn_unique (hs : B.Separated) (hA : IsSimpleCStar A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) : StateExtensionUnique B.hnnBase f :=
  B.corner_unique hs hA f hf

theorem hnn_join (hs : B.Separated) (hA : IsSimpleCStar A)
    (F G : B.HNNAlgebra →L[ℂ] ℂ) (hF : IsPureState F) (hG : IsPureState G)
    (hrF : restrictState B.hnnBase F = B.state false)
    (hrG : restrictState B.hnnBase G = B.state true) :
    PureStateEquivalent F hF G hG :=
  Peaks.join_named (B.peaks false) (B.peaks true) B.hnnBase B.hnnUnitary
    B.hnnUnitary_conjugates (B.hnn_unique hs hA _ (B.peaks true).isPureState)
    F G hF hG hrF hrG

theorem hnn_no_unintended_join (hs : B.Separated) (hA : IsSimpleCStar A)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (hne : ¬ UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg))
    (hex : ∀ i, ¬ (UnitarilyEquivalent (pureGNS f hf)
        (pureGNS (B.state i) (B.peaks i).isPureState) ∧
      UnitarilyEquivalent (pureGNS g hg)
        (pureGNS (B.state (!i)) (B.peaks (!i)).isPureState)))
    (F G : B.HNNAlgebra →L[ℂ] ℂ) (hF : IsPureState F) (hG : IsPureState G)
    (hrF : restrictState B.hnnBase F = f) (hrG : restrictState B.hnnBase G = g) :
    ¬ PureStateEquivalent F hF G hG := by
  apply corner_extensions_inequivalent_of_matrix_no_common B.embedBase f g ?_ F G hF hG hrF hrG
  intro H _ _ _ π hπ ξ η _ _ hcξ hcη
  apply B.matrix_no_unintended_join hs (NaimarkZFC.matrixState f false)
    (NaimarkZFC.matrixState g false) (matrixState_isPureState f hf false)
    (matrixState_isPureState g hg false) (B.supported_small_projections hA f hf false)
    (B.supported_small_projections hA g hg false) ?_ ?_ π hπ ξ η hcξ hcη
  · exact fun h => hne (matrix_pure_equivalence_reflects f g hf hg false false h)
  · intro i h
    exact hex i ⟨matrix_pure_equivalence_reflects f (B.state i) hf (B.peaks i).isPureState
      false i h.1, matrix_pure_equivalence_reflects g (B.state (!i)) hg
      (B.peaks (!i)).isPureState false (!i) h.2⟩

end PeakingPairData

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
  (E : C →L[ℂ] CStarMatrix Bool Bool A)

theorem matrixCornerExpectation_nonneg (hpos : ∀ c, 0 ≤ c → 0 ≤ E c)
    (x : MatrixHNNCorner φ) (hx : 0 ≤ x) : 0 ≤ matrixCornerExpectation φ E x := by
  have hp : 0 ≤ (x:C) := by
    obtain ⟨y, hy⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
    rw [hy]
    exact star_mul_self_nonneg (y:C)
  exact (matrixEntryPositive false).map_nonneg (hpos x hp)

end

open scoped ComplexOrder
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_pure_norming_state [Nontrivial A] (a : A) (ha : 0 ≤ a) :
    ∃ f : A →L[ℂ] ℂ, IsPureState f ∧ (f a).re = ‖a‖ := by
  let S : Set (WeakDual ℂ A) := {f | f ∈ weakStates A ∧ (f a).re = ‖a‖}
  have hS : IsCompact S := isCompact_weakStates.inter_right
    (isClosed_eq (Complex.continuous_re.comp (WeakDual.eval_continuous a)) continuous_const)
  have hne : S.Nonempty := by
    let : IsStarNormal a := (IsSelfAdjoint.of_nonneg ha).isStarNormal
    obtain ⟨f, hf, hnorm⟩ := exists_norming_state a
    refine ⟨StrongDual.toWeakDual f, hf, ?_⟩
    have hp := state_nonneg f hf ha
    change (f a).re = ‖a‖
    have he := Complex.norm_of_nonneg' hp
    have hre := congrArg Complex.re he
    simpa only [Complex.ofReal_re, hnorm] using hre.symm
  let : LocallyConvexSpace ℝ (WeakDual ℂ A) :=
    WeakBilin.locallyConvexSpace (B := topDualPairing ℂ A)
  obtain ⟨f, hf⟩ := hS.extremePoints_nonempty hne
  rw [mem_extremePoints] at hf
  refine ⟨f.toStrongDual, ?_, hf.1.2⟩
  rw [IsPureState, mem_extremePoints]
  refine ⟨hf.1.1, ?_⟩
  intro g hg k hk hseg
  obtain ⟨r, s, hr, hs, hrs, heq⟩ := hseg
  have hga : (g a).re ≤ ‖a‖ := (Complex.re_le_norm _).trans (state_norm_apply_le g hg a)
  have hka : (k a).re ≤ ‖a‖ := (Complex.re_le_norm _).trans (state_norm_apply_le k hk a)
  have hval := congrArg (fun l : A →L[ℂ] ℂ => (l a).re) heq
  simp only [add_apply, smul_apply, Complex.add_re, Complex.smul_re, smul_eq_mul] at hval
  change r*(g a).re+s*(k a).re = (f a).re at hval
  rw [hf.1.2] at hval
  have hscale := congrArg (fun z : ℝ => z*‖a‖) hrs
  have hgeq : (g a).re = ‖a‖ := by
    apply le_antisymm hga
    by_contra hlt
    have ht := mul_pos hr (sub_pos.mpr (lt_of_not_ge hlt))
    have hn := mul_nonneg hs.le (sub_nonneg.mpr hka)
    nlinarith
  have hkeq : (k a).re = ‖a‖ := by
    apply le_antisymm hka
    by_contra hlt
    have ht := mul_pos hs (sub_pos.mpr (lt_of_not_ge hlt))
    nlinarith
  have h := hf.2 (StrongDual.toWeakDual g) ⟨hg, hgeq⟩
    (StrongDual.toWeakDual k) ⟨hk, hkeq⟩ ⟨r,s,hr,hs,hrs, ?_⟩
  · exact ⟨congrArg WeakDual.toStrongDual h.1, congrArg WeakDual.toStrongDual h.2⟩
  · apply WeakDual.toStrongDual.injective
    exact heq

theorem positive_eq_zero_of_pure_states [Nontrivial A] (a : A) (ha : 0 ≤ a)
    (hz : ∀ f : A →L[ℂ] ℂ, IsPureState f → f a = 0) : a = 0 := by
  obtain ⟨f, hf, hnorm⟩ := exists_pure_norming_state a ha
  rw [hz f hf, Complex.zero_re] at hnorm
  exact norm_eq_zero.mp hnorm.symm

end

open scoped CStarAlgebra ComplexOrder
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in

theorem exists_contracting_real_dual {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (x : E) (hn : ‖x‖ = 1) :
    ∃ g : E →L[ℝ] ℝ, (∀ y, ‖g y‖ ≤ ‖y‖) ∧ g x = 1 := by
  obtain ⟨g,hg,hx⟩ := exists_dual_vector ℝ x (hn.trans_ne one_ne_zero)
  refine ⟨g,fun y => ?_,?_⟩
  · simpa only [hg,one_mul] using g.le_opNorm y
  · simpa [hn] using hx

def idealSelfAdjointSubspace (J : TwoSidedIdeal A) : Submodule ℝ (selfAdjoint A) where
  carrier := {a | (a:A) ∈ J}
  zero_mem' := J.zero_mem
  add_mem' ha hb := J.add_mem ha hb
  smul_mem' r a ha := by
    change r • (a:A) ∈ J
    rw [Algebra.smul_def]
    exact J.mul_mem_left _ _ ha

omit [PartialOrder A] [StarOrderedRing A] in

theorem properIdeal_one_sub_norm (J : TwoSidedIdeal A) (hJ : J ≠ ⊤)
    (a : A) (ha : a ∈ J) : 1 ≤ ‖1-a‖ := by
  by_contra hn
  have hu : IsUnit a := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one (lt_of_not_ge hn)
  obtain ⟨u,rfl⟩ := hu
  apply hJ
  apply J.eq_top
  simpa using J.mul_mem_left (↑u⁻¹) (↑u) ha

theorem exists_state_killing_ideal (J : TwoSidedIdeal A) (hc : IsClosed (J : Set A))
    (hJ : J ≠ ⊤) :
    ∃ f : A →L[ℂ] ℂ, IsState f ∧ ∀ a ∈ J, f (star a*a) = 0 := by
  let S := idealSelfAdjointSubspace J
  let : IsClosed (S : Set (selfAdjoint A)) := hc.preimage continuous_subtype_val
  let q : selfAdjoint A →L[ℝ] (selfAdjoint A ⧸ S) := S.mkQL
  have hnorm : ‖q (1 : selfAdjoint A)‖ = 1 := by
    apply le_antisymm
    · exact (Submodule.Quotient.norm_mk_le (S := S) (1 : selfAdjoint A)).trans (by exact (IsStarProjection.one A).norm_le 1)
    · apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨a,ha,hn⟩ := Submodule.Quotient.norm_mk_lt (q (1 : selfAdjoint A)) hε
      have hj : ((1 : selfAdjoint A)-a : selfAdjoint A) ∈ S :=
        (Submodule.Quotient.eq S).mp ha.symm
      have hb := properIdeal_one_sub_norm J hJ ((1 : selfAdjoint A)-a : selfAdjoint A) hj
      have hb' : 1 ≤ ‖a‖ := by
        change 1 ≤ ‖(a:A)‖
        change 1 ≤ ‖1-(1-(a:A))‖ at hb
        simpa only [sub_sub_cancel] using hb
      exact hb'.trans hn.le
  obtain ⟨g,hg,hgv⟩ := @exists_contracting_real_dual (selfAdjoint A ⧸ S)
    (Submodule.Quotient.seminormedAddCommGroup S) (Submodule.Quotient.normedSpace S ℝ)
    (q (1 : selfAdjoint A)) hnorm
  let G := g.comp q
  have hGn : ‖G‖ ≤ 1 := by
    apply G.opNorm_le_bound zero_le_one
    intro a
    calc
      ‖G a‖ ≤ ‖q a‖ := hg _
      _ ≤ 1*‖a‖ := by
        change ‖(Submodule.Quotient.mk a : selfAdjoint A ⧸ S)‖ ≤ 1*‖a‖
        simpa only [one_mul] using Submodule.Quotient.norm_mk_le (S := S) a
  have hG1 : G 1 = 1 := by
    change g (q 1) = 1
    exact hgv
  let F := selfAdjointPositive G hGn hG1
  have hF : IsState (positiveCLM F) := by
    apply (isState_iff _).mpr
    refine ⟨selfAdjointPositive_one G hGn hG1,fun a => ?_⟩
    have hh := F.map_nonneg (star_mul_self_nonneg a)
    exact ⟨hh.2.symm,hh.1⟩
  refine ⟨positiveCLM F,hF,?_⟩
  intro a ha
  let b : selfAdjoint A := ⟨star a*a,IsSelfAdjoint.of_nonneg (star_mul_self_nonneg a)⟩
  have hb : b ∈ S := J.mul_mem_left (star a) a ha
  have hq : q b = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hb
  change F (b:A) = 0
  rw [selfAdjointPositive_coe]
  change ((g (q b):ℝ):ℂ) = 0
  rw [hq,map_zero,Complex.ofReal_zero]

end

open scoped CStarAlgebra ComplexOrder InnerProductSpace
open UniformSpace
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gns_vector_zero_of_square_zero (f : A →ₚ[ℂ] ℂ) (a : A)
    (ha : f (star a*a) = 0) : f.gnsStarAlgHom a (gnsVector f) = 0 := by
  apply norm_eq_zero.mp
  rw [gns_apply_vector,Completion.norm_coe,PositiveLinearMap.preGNS_norm_def,
    PositiveLinearMap.ofPreGNS_toPreGNS,ha,Complex.zero_re,Real.sqrt_zero]

theorem gns_kills_ideal (f : A →ₚ[ℂ] ℂ) (J : TwoSidedIdeal A)
    (hf : ∀ a ∈ J, f (star a*a) = 0) (a : A) (ha : a ∈ J) :
    f.gnsStarAlgHom a = 0 := by
  apply DFunLike.coe_injective
  apply (gnsVector_cyclic f).equalizer ((f.gnsStarAlgHom a).continuous) (by fun_prop)
  funext b
  change f.gnsStarAlgHom a (f.gnsStarAlgHom b (gnsVector f)) = 0
  rw [← mul_apply_eq_comp,← map_mul]
  exact gns_vector_zero_of_square_zero f (a*b) (hf _ (J.mul_mem_right a b ha))

end

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem simple_extension_of_uep_expectation (hA : IsSimpleCStar A)
    (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ) (E : C →L[ℂ] A)
    (hfix : ∀ a, E (φ a) = a)
    (hpos : ∀ c, 0 ≤ c → 0 ≤ E c)
    (hfaith : ∀ c, E (star c*c) = 0 → c = 0)
    (hstate : ∀ f : A →L[ℂ] ℂ, IsState f → IsState (f.comp E))
    (hu : ∀ f : A →L[ℂ] ℂ, IsPureState f → StateExtensionUnique φ f) :
    IsSimpleCStar C := by
  let : Nontrivial A := hA.1
  let : Nontrivial C := Function.Injective.nontrivial hφ
  refine ⟨inferInstance,fun J hc => ?_⟩
  by_cases hJ : J = ⊤
  · exact Or.inr hJ
  left
  obtain ⟨f,hf,hkill⟩ := exists_state_killing_ideal J hc hJ
  let F : C →ₚ[ℂ] ℂ := positiveOfSquares f hf.2
  let π := F.gnsStarAlgHom
  have hn : ‖gnsVector F‖ = 1 := gnsVector_norm_eq_one F ((isState_iff f).mp hf).1
  have hπ : (π.comp φ).toNonUnitalStarAlgHom ≠ 0 := by
    intro hz
    have hh := congrArg (fun ψ : A →⋆ₙₐ[ℂ] (F.GNS →L[ℂ] F.GNS) =>
      ψ 1 (gnsVector F)) hz
    have hh' : gnsVector F = 0 := by
      change π (φ 1) (gnsVector F) = 0 at hh
      simpa only [map_one,one_apply_eq_self] using hh
    rw [hh',norm_zero] at hn
    exact zero_ne_one hn
  have hinj : Function.Injective (π.comp φ) :=
    simple_nonzeroStarHom_injective hA (π.comp φ).toNonUnitalStarAlgHom hπ
  have hπJ : ∀ a ∈ J, π a = 0 := gns_kills_ideal F J hkill
  have hEJ : ∀ a ∈ J, E (star a*a) = 0 := by
    intro a ha
    apply positive_eq_zero_of_pure_states _ (hpos _ (star_mul_self_nonneg a))
    intro g hg
    obtain ⟨G,hG,hGr⟩ := exists_state_extension_of_injective (π.comp φ) hinj g hg.1
    let k := restrictState π G
    have hk : IsState k := isState_restrict π G hG
    have hkr : restrictState φ k = g := hGr
    have hEr : restrictState φ (g.comp E) = g := by
      ext b
      exact congrArg g (hfix b)
    have he : g.comp E = k := hu g hg _ _ (hstate g hg.1) hk hEr hkr
    have hh := congrArg (fun z : C →L[ℂ] ℂ => z (star a*a)) he
    change g (E (star a*a)) = G (π (star a*a)) at hh
    rw [map_mul π,hπJ a ha,mul_zero,map_zero] at hh
    exact hh
  apply le_antisymm _ bot_le
  intro a ha
  have hz := hfaith a (hEJ a ha)
  rw [hz]
  exact TwoSidedIdeal.zero_mem _

end

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem simple_extension_of_uep_square_expectation (hA : IsSimpleCStar A)
    (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ) (E : C →L[ℂ] A)
    (hfix : ∀ a, E (φ a) = a)
    (hpos : ∀ c, 0 ≤ E (star c*c))
    (hfaith : ∀ c, E (star c*c) = 0 → c = 0)
    (hstate : ∀ f : A →L[ℂ] ℂ, IsState f → IsState (f.comp E))
    (hu : ∀ f : A →L[ℂ] ℂ, IsPureState f → StateExtensionUnique φ f) :
    IsSimpleCStar C := by
  apply simple_extension_of_uep_expectation hA φ hφ E hfix ?_ hfaith hstate hu
  intro c hc
  obtain ⟨x,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hc
  exact hpos x
end

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem expectCorner_square_nonneg (x : B.Corner) : 0 ≤ B.expectCorner (star x*x) := by
  apply (matrixEntryPositive false).map_nonneg
  apply atomicExpectation_nonneg B.atoms B.amalgam false
  change 0 ≤ star ((x:B.Model):B.Operators)*((x:B.Model):B.Operators)
  exact star_mul_self_nonneg _

theorem corner_simple (hs : B.Separated) (hA : IsSimpleCStar A) : IsSimpleCStar B.Corner :=
  simple_extension_of_uep_square_expectation hA B.cornerBase B.cornerBase_injective B.expectCorner
    B.expectCorner_base B.expectCorner_square_nonneg B.expectCorner_faithful B.expectCorner_state
    (B.corner_unique hs hA)

end PeakingPairData

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
  (E : C →L[ℂ] CStarMatrix Bool Bool A)

theorem matrixCornerExpectation_left
    (hleft : ∀ a x, E (φ a*x) = a*E x)
    (hright : ∀ x a, E (x*φ a) = E x*a) (a : A) (x : MatrixHNNCorner φ) :
    matrixCornerExpectation φ E (matrixCornerBase φ a*x) = a*matrixCornerExpectation φ E x := by
  change E (φ (matrixSingle false false a)*(x:C)) false false = _
  rw [hleft,matrixCornerExpectation_supported φ E hleft hright x,matrixSingle_mul,
    matrixSingle_apply,ite_eq_left ⟨rfl,rfl⟩]

theorem matrixCornerExpectation_right
    (hleft : ∀ a x, E (φ a*x) = a*E x)
    (hright : ∀ x a, E (x*φ a) = E x*a) (x : MatrixHNNCorner φ) (a : A) :
    matrixCornerExpectation φ E (x*matrixCornerBase φ a) = matrixCornerExpectation φ E x*a := by
  change E ((x:C)*φ (matrixSingle false false a)) false false = _
  rw [hright,matrixCornerExpectation_supported φ E hleft hright x,matrixSingle_mul,
    matrixSingle_apply,ite_eq_left ⟨rfl,rfl⟩]

namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem hnnExpectation_left (a : A) (x : B.HNNAlgebra) :
    B.hnnExpectation (B.hnnBase a*x) = a*B.hnnExpectation x :=
  matrixCornerExpectation_left B.embedBase B.modelExpectation
    (atomicExpectation_factor_mul B.atoms B.amalgam false)
    (atomicExpectation_mul_factor B.atoms B.amalgam false) a x

theorem hnnExpectation_right (x : B.HNNAlgebra) (a : A) :
    B.hnnExpectation (x*B.hnnBase a) = B.hnnExpectation x*a :=
  matrixCornerExpectation_right B.embedBase B.modelExpectation
    (atomicExpectation_factor_mul B.atoms B.amalgam false)
    (atomicExpectation_mul_factor B.atoms B.amalgam false) x a

theorem hnnExpectation_square_nonneg (x : B.HNNAlgebra) : 0 ≤ B.hnnExpectation (star x*x) :=
  B.expectCorner_square_nonneg x

theorem hnnExpectation_faithful (x : B.HNNAlgebra) (hx : B.hnnExpectation (star x*x) = 0) : x = 0 :=
  B.expectCorner_faithful x hx

theorem hnn_simple (hs : B.Separated) (hA : IsSimpleCStar A) : IsSimpleCStar B.HNNAlgebra :=
  B.corner_simple hs hA

end PeakingPairData
end

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem pure_lifts_equivalent (φ : A →⋆ₐ[ℂ] C)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (he : UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg))
    (hu : StateExtensionUnique φ g)
    (F G : C →L[ℂ] ℂ) (hF : IsPureState F) (hG : IsPureState G)
    (hrF : restrictState φ F = f) (hrG : restrictState φ G = g) :
    UnitarilyEquivalent (pureGNS F hF) (pureGNS G hG) := by
  obtain ⟨u,huconj⟩ := pureState_equivalent_conjugate f g hf hg he
  let v : unitary C := ⟨φ (u:A),by
    constructor
    · rw [← map_star,← map_mul,u.property.1,map_one]
    · rw [← map_star,← map_mul,u.property.2,map_one]⟩
  let H := restrictState (Unitary.conjStarAlgAut ℂ C v).symm.toStarAlgHom F
  have hH : IsState H := isState_restrict _ _ hF.1
  have hrH : restrictState φ H = g := by
    ext a
    change F (star (φ (u:A))*φ a*φ (u:A)) = g a
    rw [← map_star,← map_mul,← map_mul]
    change restrictState φ F (star (u:A)*a*(u:A)) = g a
    rw [hrF]
    exact (congrArg (fun k : A →L[ℂ] ℂ => k a) huconj).symm
  have hh := hu H G hH hG.1 hrH hrG
  apply pureState_equivalent_of_conjugate F G hF hG v
  intro a
  exact (congrArg (fun k : C →L[ℂ] ℂ => k a) hh).symm

end

open Topology
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

def PureUEP (φ : A →⋆ₐ[ℂ] B) : Prop :=
  ∀ f : A →L[ℂ] ℂ, IsPureState f → StateExtensionUnique φ f

@[simp] theorem restrictState_comp (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C)
    (f : C →L[ℂ] ℂ) : restrictState φ (restrictState ψ f) = restrictState (ψ.comp φ) f := by
  ext a
  rfl

theorem PureUEP.comp {φ : A →⋆ₐ[ℂ] B} {ψ : B →⋆ₐ[ℂ] C}
    (hφ : PureUEP φ) (hψ : PureUEP ψ) : PureUEP (ψ.comp φ) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  intro f hf F G hF hG hrF hrG
  let fB := restrictState ψ F
  have hfB : IsState fB := isState_restrict ψ F hF
  have hrB : restrictState φ fB = f := by
    change restrictState φ (restrictState ψ F) = f
    rw [restrictState_comp,hrF]
  have huni : ∀ g : B →L[ℂ] ℂ, IsState g → restrictState φ g = f → g = fB :=
    fun g hg hr => hφ f hf g fB hg hfB hr hrB
  have hpB : IsPureState fB := unique_lift_pure φ f hf fB hfB hrB huni
  have heq : restrictState ψ G = fB :=
    huni _ (isState_restrict ψ G hG) (by rw [restrictState_comp,hrG])
  exact hψ fB hpB F G hF hG rfl heq

theorem PureUEP.id : PureUEP (StarAlgHom.id ℂ A) := by
  intro f _ F G _ _ hF hG
  have hF' : F = f := by
    ext a
    exact congrArg (fun h : A →L[ℂ] ℂ => h a) hF
  have hG' : G = f := by
    ext a
    exact congrArg (fun h : A →L[ℂ] ℂ => h a) hG
  exact hF'.trans hG'.symm

theorem PureUEP.of_dense_cover {ι : Type*} (D : ι → Type*)
    [∀ i, CStarAlgebra (D i)]
    (φ : A →⋆ₐ[ℂ] C) (incl : ∀ i, A →⋆ₐ[ℂ] D i) (into : ∀ i, D i →⋆ₐ[ℂ] C)
    (hcomp : ∀ i, (into i).comp (incl i) = φ)
    (hU : ∀ i, PureUEP (incl i))
    (hd : Dense (⋃ i, Set.range (into i))) : PureUEP φ := by
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  let (i : ι) : PartialOrder (D i) := CStarAlgebra.spectralOrder (D i)
  let (i : ι) : StarOrderedRing (D i) := CStarAlgebra.spectralOrderedRing (D i)
  intro f hf F G hF hG hrF hrG
  apply ContinuousLinearMap.ext
  intro x
  apply closure_minimal (t := {z | F z = G z}) ?_
    (isClosed_eq F.continuous G.continuous) (hd x)
  intro x hx
  obtain ⟨i,a,rfl⟩ := Set.mem_iUnion.mp hx
  have hri (H : C →L[ℂ] ℂ) (hH : restrictState φ H = f) :
      restrictState (incl i) (restrictState (into i) H) = f := by
    rw [restrictState_comp,hcomp,hH]
  have hi := hU i f hf (restrictState (into i) F) (restrictState (into i) G)
    (isState_restrict _ _ hF) (isState_restrict _ _ hG) (hri F hrF) (hri G hrG)
  exact congrArg (fun u : D i →L[ℂ] ℂ => u a) hi

end

open scoped CStarAlgebra ComplexOrder
section
universe u v w
variable {I : Type u} [Nonempty I] (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  {C : Type w} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem simple_of_dense_stage_ranges (hA : ∀ i, IsSimpleCStar (A i))
    (φ : ∀ i, A i →⋆ₐ[ℂ] C) (hi : ∀ i, Isometry (φ i))
    (hd : Dense (⋃ i, Set.range (φ i))) : IsSimpleCStar C := by
  let i₀ : I := Classical.choice inferInstance
  let : Nontrivial (A i₀) := (hA i₀).1
  let : Nontrivial C := (hi i₀).injective.nontrivial
  refine ⟨inferInstance,fun J hc => ?_⟩
  by_cases hJ : J = ⊤
  · exact Or.inr hJ
  left
  obtain ⟨g,hg,hkill⟩ := exists_state_killing_ideal J hc hJ
  let G : C →ₚ[ℂ] ℂ := positiveOfSquares g hg.2
  let π := G.gnsStarAlgHom
  have hn : ‖gnsVector G‖ = 1 := gnsVector_norm_eq_one G ((isState_iff g).mp hg).1
  have hstage (i : I) : Function.Injective (π.comp (φ i)) := by
    apply simple_nonzeroStarHom_injective (hA i) (π.comp (φ i)).toNonUnitalStarAlgHom
    intro hz
    have hh := congrArg (fun ψ : A i →⋆ₙₐ[ℂ] (G.GNS →L[ℂ] G.GNS) =>
      ψ 1 (gnsVector G)) hz
    have hh' : gnsVector G = 0 := by
      change π (φ i 1) (gnsVector G) = 0 at hh
      simpa only [map_one,one_apply_eq_self] using hh
    rw [hh',norm_zero] at hn
    exact zero_ne_one hn
  have hnorm (c : C) : ‖π c‖ = ‖c‖ := by
    apply (closure_minimal ?_ (isClosed_eq ((map_continuous π).norm) continuous_norm)) (hd c)
    intro c hc'
    obtain ⟨i,a,rfl⟩ := Set.mem_iUnion.mp hc'
    exact (NonUnitalStarAlgHom.norm_map (π.comp (φ i)) (hstage i) a).trans
      ((hi i).norm_map_of_map_zero (map_zero _) a).symm
  apply le_antisymm _ bot_le
  intro a ha
  have hz : π a = 0 := gns_kills_ideal G J hkill a ha
  have hna := hnorm a
  rw [hz,norm_zero] at hna
  rw [norm_eq_zero.mp hna.symm]
  exact TwoSidedIdeal.zero_mem _

end

open Topology
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

theorem StateExtensionUnique.postcomp_equiv
    {φ : A →⋆ₐ[ℂ] B} {f : A →L[ℂ] ℂ} (hu : StateExtensionUnique φ f)
    (e : B ≃⋆ₐ[ℂ] C) : StateExtensionUnique (e.toStarAlgHom.comp φ) f := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  intro F G hF hG hrF hrG
  have he := hu (restrictState e.toStarAlgHom F) (restrictState e.toStarAlgHom G)
    (isState_restrict _ _ hF) (isState_restrict _ _ hG)
    (by rw [restrictState_comp]; exact hrF) (by rw [restrictState_comp]; exact hrG)
  ext c
  obtain ⟨b,rfl⟩ := e.surjective c
  exact congrArg (fun h : B →L[ℂ] ℂ => h b) he

theorem PureUEP.postcomp_equiv {φ : A →⋆ₐ[ℂ] B}
    (hu : PureUEP φ) (e : B ≃⋆ₐ[ℂ] C) : PureUEP (e.toStarAlgHom.comp φ) :=
  fun f hf => (hu f hf).postcomp_equiv e

theorem IsSimpleCStar.of_equiv (hA : IsSimpleCStar A) (e : A ≃⋆ₐ[ℂ] B) :
    IsSimpleCStar B := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  apply simple_of_dense_stage_ranges (fun _ : Unit => A) (fun _ => hA)
    (fun _ => e.toStarAlgHom) (fun _ => StarAlgEquiv.isometry e)
  have he : (⋃ _ : Unit, Set.range e.toStarAlgHom) = Set.univ := by
    ext b
    simp only [Set.mem_iUnion,Set.mem_range,Set.mem_univ,iff_true]
    obtain ⟨a,ha⟩ := e.surjective b
    exact ⟨(),a,ha⟩
  rw [he]
  exact dense_univ

end

open Topology
section
universe u v

theorem pureUEP_ordinal_chain
    (A : Ordinal.{u} → Type v) [∀ i, CStarAlgebra (A i)]
    (incl : ∀ {i j : Ordinal.{u}}, i ≤ j → A i →⋆ₐ[ℂ] A j)
    (hid : ∀ i, incl (le_refl i) = StarAlgHom.id ℂ (A i))
    (hcomp : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k),
      (incl hjk).comp (incl hij) = incl (hij.trans hjk))
    (L : Ordinal.{u})
    (hnext : ∀ i < L, PureUEP (incl (show i ≤ i+1 by exact le_self_add)))
    (hcont : ∀ j ≤ L, Order.IsSuccLimit j →
      Dense (⋃ k : {k : Ordinal.{u} // k < j}, Set.range (incl k.property.le)))
    (j : Ordinal.{u}) (hj : j ≤ L) (i : Ordinal.{u}) (hij : i ≤ j) :
    PureUEP (incl hij) := by
  induction j using Ordinal.limitRecOn generalizing i with
  | zero =>
    have hi : i = 0 := le_antisymm hij bot_le
    subst i
    rw [hid]
    exact PureUEP.id
  | add_one j ih =>
    by_cases he : i = j+1
    · subst i
      rw [hid]
      exact PureUEP.id
    · have hlt : i < j+1 := lt_of_le_of_ne hij he
      have hi : i ≤ j := by simpa only [Order.lt_add_one_iff] using hlt
      have hjL : j < L := (show j < j+1 from lt_add_one j).trans_le hj
      have hu := (ih hjL.le i hi).comp (hnext j hjL)
      rwa [hcomp] at hu
  | limit j hjlim ih =>
    by_cases he : i = j
    · subst i
      rw [hid]
      exact PureUEP.id
    · have hi : i < j := lt_of_le_of_ne hij he
      let J := {k : Ordinal.{u} // i ≤ k ∧ k < j}
      have hd : Dense (⋃ k : J, Set.range (incl k.property.2.le)) := by
        apply (hcont j hj hjlim).mono
        intro a ha
        obtain ⟨k,b,rfl⟩ := Set.mem_iUnion.mp ha
        let m : J := ⟨max i k.val,le_max_left _ _,max_lt hi k.property⟩
        apply Set.mem_iUnion.mpr
        refine ⟨m, incl (le_max_right i k.val) b, ?_⟩
        have hh := congrArg (fun φ : A k.val →⋆ₐ[ℂ] A j => φ b)
          (hcomp (le_max_right i k.val) m.property.2.le)
        exact hh
      exact PureUEP.of_dense_cover (fun k : J => A k.val) (incl hij)
        (fun k => incl k.property.1) (fun k => incl k.property.2.le)
        (fun k => hcomp k.property.1 k.property.2.le)
        (fun k => ih k.val k.property.2 (k.property.2.le.trans hj) i k.property.1) hd

end

open Topology
section

inductive BridgeSuccessor {A C : Type} [CStarAlgebra A] [CStarAlgebra C]
    [PartialOrder A] [StarOrderedRing A] (φ : A →⋆ₐ[ℂ] C) : Prop
  | identity (e : A ≃⋆ₐ[ℂ] C) (he : ∀ a, e a = φ a)
  | hnn (B : PeakingPairData A) (hs : B.Separated)
      (e : B.HNNAlgebra ≃⋆ₐ[ℂ] C) (he : ∀ a, e (B.hnnBase a) = φ a)

theorem BridgeSuccessor.properties {A C : Type} [CStarAlgebra A] [CStarAlgebra C]
    [PartialOrder A] [StarOrderedRing A] {φ : A →⋆ₐ[ℂ] C}
    (h : BridgeSuccessor φ) (hA : IsSimpleCStar A) :
    Function.Injective φ ∧ IsSimpleCStar C ∧ PureUEP φ := by
  cases h with
  | identity e he =>
    have hh : φ = e.toStarAlgHom := by ext a; exact (he a).symm
    rw [hh]
    refine ⟨e.injective,hA.of_equiv e,?_⟩
    simpa only [StarAlgHom.comp_id] using (PureUEP.id (A := A)).postcomp_equiv e
  | hnn B hs e he =>
    have hh : φ = e.toStarAlgHom.comp B.hnnBase := by ext a; exact (he a).symm
    rw [hh]
    exact ⟨e.injective.comp B.hnnBase_injective,(B.hnn_simple hs hA).of_equiv e,
      (show PureUEP B.hnnBase from fun f hf => B.hnn_unique hs hA f hf).postcomp_equiv e⟩

universe u
variable (A : Ordinal.{u} → Type) [∀ i, CStarAlgebra (A i)]
    [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
    (incl : ∀ {i j : Ordinal.{u}}, i ≤ j → A i →⋆ₐ[ℂ] A j)
    (L : Ordinal.{u})
    (hbase : IsSimpleCStar (A 0))
    (hnext : ∀ i < L, BridgeSuccessor (incl (show i ≤ i+1 by exact le_self_add)))
    (hi : ∀ {i j} (h : i ≤ j), Function.Injective (incl h))
    (hcont : ∀ j ≤ L, Order.IsSuccLimit j →
      Dense (⋃ k : {k : Ordinal.{u} // k < j}, Set.range (incl k.property.le)))

include hbase hnext hi hcont in

theorem bridge_ordinal_simple (j : Ordinal.{u}) (hj : j ≤ L) : IsSimpleCStar (A j) := by
  induction j using Ordinal.limitRecOn with
  | zero => exact hbase
  | add_one j ih =>
    have hjL : j < L := (lt_add_one j).trans_le hj
    exact ((hnext j hjL).properties (ih hjL.le)).2.1
  | limit j hjlim ih =>
    let J := {k : Ordinal.{u} // k < j}
    let : Nonempty J := ⟨⟨0,hjlim.ne_bot.bot_lt⟩⟩
    exact simple_of_dense_stage_ranges (fun k : J => A k.val)
      (fun k => ih k.val k.property (k.property.le.trans hj))
      (fun k => incl k.property.le)
      (fun k => NonUnitalStarAlgHom.isometry _ (hi k.property.le)) (hcont j hj hjlim)

include hbase hnext hi hcont in

theorem bridge_ordinal_pureUEP
    (hid : ∀ i, incl (le_refl i) = StarAlgHom.id ℂ (A i))
    (hcomp : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k),
      (incl hjk).comp (incl hij) = incl (hij.trans hjk))
    (j : Ordinal.{u}) (hj : j ≤ L) (i : Ordinal.{u}) (hij : i ≤ j) :
    PureUEP (incl hij) := by
  apply pureUEP_ordinal_chain A incl hid hcomp L _ hcont j hj i hij
  intro k hk
  exact ((hnext k hk).properties (bridge_ordinal_simple A incl L hbase hnext hi hcont k hk.le)).2.2

end

section
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem StateExtensionUnique.of_surjective (φ : A →⋆ₐ[ℂ] B)
    (hs : Function.Surjective φ) (f : A →L[ℂ] ℂ) : StateExtensionUnique φ f := by
  intro F G _ _ hF hG
  ext b
  obtain ⟨a,rfl⟩ := hs b
  exact (congrArg (fun h : A →L[ℂ] ℂ => h a) hF).trans
    (congrArg (fun h : A →L[ℂ] ℂ => h a) hG).symm

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem isPureState_restrict_equiv (e : A ≃⋆ₐ[ℂ] B)
    (f : B →L[ℂ] ℂ) (hf : IsPureState f) :
    IsPureState (restrictState e.toStarAlgHom f) := by
  have hr : restrictState e.symm.toStarAlgHom (restrictState e.toStarAlgHom f) = f := by
    ext b
    exact congrArg f (e.apply_symm_apply b)
  exact unique_lift_pure e.symm.toStarAlgHom f hf _
    (isState_restrict e.toStarAlgHom f hf.1) hr (fun g hg hgr =>
      StateExtensionUnique.of_surjective e.symm.toStarAlgHom e.symm.surjective f
        g _ hg (isState_restrict _ _ hf.1) hgr hr)

theorem pureStateEquivalent_restrict_equiv (e : A ≃⋆ₐ[ℂ] B)
    (f g : B →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (he : PureStateEquivalent f hf g hg) :
    PureStateEquivalent (restrictState e.toStarAlgHom f) (isPureState_restrict_equiv e f hf)
      (restrictState e.toStarAlgHom g) (isPureState_restrict_equiv e g hg) := by
  exact pure_lifts_equivalent e.symm.toStarAlgHom f g hf hg he
    (StateExtensionUnique.of_surjective _ e.symm.surjective g) _ _
    (isPureState_restrict_equiv e f hf) (isPureState_restrict_equiv e g hg)
    (by ext b; exact congrArg f (e.apply_symm_apply b))
    (by ext b; exact congrArg g (e.apply_symm_apply b))

end

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule CStarAlgebra
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in

theorem mixed_zero_of_state_cross_decay {ι : Type*} {l : Filter ι} [l.NeBot]
    (f g : A →L[ℂ] ℂ) (x y : ι → A)
    (hx : ∀ i, IsSelfAdjoint (x i)) (hxn : ∀ i, ‖x i‖ ≤ 1) (hyn : ∀ i, ‖y i‖ ≤ 1)
    (hxv : ∀ i, f (x i) = 1) (hyv : ∀ i, g (y i) = 1)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hcξ : ∀ a, ⟪ξ,π a ξ⟫_ℂ = f a) (hcη : ∀ a, ⟪η,π a η⟫_ℂ = g a)
    (a : A) (hdec : Tendsto (fun i => x i*a*y i) l (𝓝 0)) :
    ⟪ξ,π a η⟫_ℂ = 0 := by
  let L : A →L[ℂ] ℂ := (innerSL ℂ ξ).comp (orbitCLM π η)
  have he (i) : L (x i*a*y i) = L a :=
    representation_coefficient_compression π ξ η _ _ _ (hx i)
      (representation_fix_of_coefficient_one π ξ hξ _ (hxn i) ((hcξ _).trans (hxv i)))
      (representation_fix_of_coefficient_one π η hη _ (hyn i) ((hcη _).trans (hyv i)))
  have ht : Tendsto (fun _ : ι => L a) l (𝓝 0) := by
    simpa only [Function.comp_def,he,map_zero] using (L.continuous.tendsto 0).comp hdec
  exact tendsto_nhds_unique tendsto_const_nhds ht

omit [PartialOrder A] [StarOrderedRing A] in

theorem pureExcisionNet_value
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (ξ : H) (hξ : ‖ξ‖ = 1) (i : ExcisionIndex (vectorNullAlgebra π ξ)) :
    ⟪ξ,π (pureExcisionNet π ξ i) ξ⟫_ℂ = 1 := by
  rw [pureExcisionNet_fixes π hone ξ i,inner_self_eq_norm_sq_to_K,hξ]
  norm_num

theorem inequivalent_pure_mixed_zero
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (hne : ¬ PureStateEquivalent f hf g hg)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hcξ : ∀ a, ⟪ξ,π a ξ⟫_ℂ = f a) (hcη : ∀ a, ⟪η,π a η⟫_ℂ = g a)
    (a : A) : ⟪ξ,π a η⟫_ℂ = 0 := by
  let F := positiveOfSquares f hf.1.2
  let G := positiveOfSquares g hg.1.2
  let ζ := gnsVector F
  let ν := gnsVector G
  let x := pureExcisionNet F.gnsNonUnitalStarAlgHom ζ
  let y := pureExcisionNet G.gnsNonUnitalStarAlgHom ν
  have hxv (i) : f (x i) = 1 :=
    (gnsVector_coefficient F _).symm.trans
      (pureExcisionNet_value _ (irreducible_map_one _ (pure_gns_irreducible f hf.1 hf)) ζ
        (gnsVector_norm_eq_one F ((isState_iff f).mp hf.1).1) i)
  have hyv (i) : g (y i) = 1 :=
    (gnsVector_coefficient G _).symm.trans
      (pureExcisionNet_value _ (irreducible_map_one _ (pure_gns_irreducible g hg.1 hg)) ν
        (gnsVector_norm_eq_one G ((isState_iff g).mp hg.1).1) i)
  let : (atTop : Filter (ExcisionIndex (vectorNullAlgebra F.gnsNonUnitalStarAlgHom ζ) ×
      ExcisionIndex (vectorNullAlgebra G.gnsNonUnitalStarAlgHom ν))).NeBot := by
    rw [← Filter.prod_atTop_atTop_eq]
    infer_instance
  apply mixed_zero_of_state_cross_decay f g (fun ij : ExcisionIndex (vectorNullAlgebra F.gnsNonUnitalStarAlgHom ζ) ×
      ExcisionIndex (vectorNullAlgebra G.gnsNonUnitalStarAlgHom ν) => x ij.1) (fun ij => y ij.2)
      (l := (atTop : Filter (ExcisionIndex (vectorNullAlgebra F.gnsNonUnitalStarAlgHom ζ) ×
        ExcisionIndex (vectorNullAlgebra G.gnsNonUnitalStarAlgHom ν))))
      (fun ij => IsSelfAdjoint.of_nonneg (pureExcisionNet_nonneg _ _ ij.1))
      (fun ij => pureExcisionNet_norm _ _ ij.1)
      (fun ij => pureExcisionNet_norm _ _ ij.2)
      (fun ij => hxv ij.1)
      (fun ij => hyv ij.2) π ξ η hξ hη hcξ hcη a
  exact pureExcisionNet_cross _ (pure_gns_irreducible f hf.1 hf) ζ
    (gnsVector_norm_eq_one F ((isState_iff f).mp hf.1).1)
    _ (pure_gns_irreducible g hg.1 hg) ν
    (gnsVector_norm_eq_one G ((isState_iff g).mp hg.1).1) hne a

variable {ι : Type*} (B : ι → Type*) [∀ i, CStarAlgebra (B i)]
    [∀ i, PartialOrder (B i)] [∀ i, StarOrderedRing (B i)]

theorem pure_inequivalent_of_dense_restrictions
    (φ : ∀ i, B i →⋆ₐ[ℂ] A)
    (hd : Dense (⋃ i, Set.range (φ i)))
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (hfr : ∀ i, IsPureState (restrictState (φ i) f))
    (hgr : ∀ i, IsPureState (restrictState (φ i) g))
    (hne : ∀ i, ¬ PureStateEquivalent _ (hfr i) _ (hgr i)) :
    ¬ PureStateEquivalent f hf g hg := by
  apply pure_extensions_inequivalent_of_no_common (StarAlgHom.id ℂ A) f g (g₁ := f) (g₂ := g)
      (hg₁ := hf) (hg₂ := hg) (hr₁ := rfl) (hr₂ := rfl)
  intro K _ _ _ π hπ ξ η hξ hη hcξ hcη
  let L : A →L[ℂ] ℂ := (innerSL ℂ ξ).comp (orbitCLM π η)
  have hL : L = 0 := by
    apply ContinuousLinearMap.ext
    intro a
    apply (closure_minimal ?_ (isClosed_eq L.continuous continuous_const)) (hd a)
    intro b hb
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hb
    obtain ⟨b,rfl⟩ := hi
    exact inequivalent_pure_mixed_zero _ _ (hfr i) (hgr i) (hne i)
      (π.comp (φ i).toNonUnitalStarAlgHom) ξ η hξ hη
      (fun b => hcξ (φ i b)) (fun b => hcη (φ i b)) b
  have hη0 : η ≠ 0 := norm_ne_zero_iff.mp (hη.trans_ne one_ne_zero)
  have hh : ⟪ξ,ξ⟫_ℂ = 0 :=
    (irreducible_vector_cyclic π hπ η hη0).induction_on
      (p := fun v => ⟪ξ,v⟫_ℂ = 0) ξ
      (isClosed_eq (innerSL ℂ ξ).continuous continuous_const)
      (fun a => congrArg (fun T : A →L[ℂ] ℂ => T a) hL)
  have hz : ξ = 0 := inner_self_eq_zero.mp hh
  simp only [hz,norm_zero,zero_ne_one] at hξ

end

open Topology
section
universe u v

theorem pure_inequivalent_ordinal_chain
    (A : Ordinal.{u} → Type v) [∀ i, CStarAlgebra (A i)]
    [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
    (incl : ∀ {i j : Ordinal.{u}}, i ≤ j → A i →⋆ₐ[ℂ] A j)
    (hcomp : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k),
      (incl hjk).comp (incl hij) = incl (hij.trans hjk))
    (L i₀ : Ordinal.{u})
    (f g : ∀ i, A i →L[ℂ] ℂ) (hf : ∀ i, IsPureState (f i)) (hg : ∀ i, IsPureState (g i))
    (hfr : ∀ {i j} (h : i ≤ j), restrictState (incl h) (f j) = f i)
    (hgr : ∀ {i j} (h : i ≤ j), restrictState (incl h) (g j) = g i)
    (hinit : ¬ PureStateEquivalent (f i₀) (hf i₀) (g i₀) (hg i₀))
    (hnext : ∀ i < L, i₀ ≤ i →
      (¬ PureStateEquivalent (f i) (hf i) (g i) (hg i)) →
      ¬ PureStateEquivalent (f (i+1)) (hf (i+1)) (g (i+1)) (hg (i+1)))
    (hcont : ∀ j ≤ L, Order.IsSuccLimit j →
      Dense (⋃ k : {k : Ordinal.{u} // k < j}, Set.range (incl k.property.le)))
    (j : Ordinal.{u}) (hj : j ≤ L) (hij : i₀ ≤ j) :
    ¬ PureStateEquivalent (f j) (hf j) (g j) (hg j) := by
  induction j using Ordinal.limitRecOn with
  | zero =>
    have he : i₀ = 0 := le_antisymm hij bot_le
    subst i₀
    exact hinit
  | add_one j ih =>
    by_cases he : i₀ = j+1
    · subst i₀; exact hinit
    · have hi : i₀ ≤ j := by
        simpa only [Order.lt_add_one_iff] using (lt_of_le_of_ne hij he)
      exact hnext j ((lt_add_one j).trans_le hj) hi (ih (le_self_add.trans hj) hi)
  | limit j hjlim ih =>
    by_cases he : i₀ = j
    · subst i₀; exact hinit
    · have hi : i₀ < j := lt_of_le_of_ne hij he
      let J := {k : Ordinal.{u} // i₀ ≤ k ∧ k < j}
      have hd : Dense (⋃ k : J, Set.range (incl k.property.2.le)) := by
        apply (hcont j hj hjlim).mono
        intro a ha
        obtain ⟨k,b,rfl⟩ := Set.mem_iUnion.mp ha
        let m : J := ⟨max i₀ k.val,le_max_left _ _,max_lt hi k.property⟩
        apply Set.mem_iUnion.mpr
        refine ⟨m,incl (le_max_right i₀ k.val) b,?_⟩
        exact congrArg (fun φ : A k.val →⋆ₐ[ℂ] A j => φ b)
          (hcomp (le_max_right i₀ k.val) m.property.2.le)
      apply pure_inequivalent_of_dense_restrictions (fun k : J => A k.val)
        (fun k => incl k.property.2.le) hd (f j) (g j) (hf j) (hg j)
        (fun k => by rw [hfr]; exact hf k.val)
        (fun k => by rw [hgr]; exact hg k.val)
      intro k
      simpa only [hfr,hgr] using ih k.val k.property.2 (k.property.2.le.trans hj) k.property.1

end

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem Peaks.extend {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (φ : A →⋆ₐ[ℂ] C) (hu : StateExtensionUnique φ f)
    (F : C →L[ℂ] ℂ) (hF : IsState F) (hr : restrictState φ F = f) :
    Peaks (fun n => φ (p n)) F := by
  refine ⟨fun n => (hp.1 n).map φ, fun m n h => OrderHomClass.mono φ (hp.2.1 h),
    hF, ?_, ?_⟩
  · intro n
    change restrictState φ F (p n) = 1
    rw [hr]
    exact hp.2.2.2.1 n
  · intro G hG hGp
    have hGres : restrictState φ G = f := hp.2.2.2.2 _ (isState_restrict φ G hG) hGp
    exact hu G F hG hF hGres hr

theorem Peaks.restrict (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ)
    {p : ℕ → A} {F : C →L[ℂ] ℂ} (hp : Peaks (fun n => φ (p n)) F) :
    Peaks p (restrictState φ F) ∧ StateExtensionUnique φ (restrictState φ F) := by
  have hn (G : C →L[ℂ] ℂ) (hG : IsState G)
      (hr : restrictState φ G = restrictState φ F) : G = F := by
    apply hp.2.2.2.2 G hG
    intro n
    change restrictState φ G (p n) = 1
    rw [hr]
    exact hp.2.2.2.1 n
  refine ⟨⟨?_, ?_, isState_restrict φ F hp.2.2.1, hp.2.2.2.1, ?_⟩, ?_⟩
  · intro n
    refine ⟨?_, ?_⟩
    · apply hφ
      rw [map_mul]
      exact (hp.1 n).isIdempotentElem
    · apply hφ
      rw [map_star]
      exact (hp.1 n).isSelfAdjoint
  · intro m n h
    apply sub_nonneg.mp
    apply (faithfulStarHom_nonneg_iff φ hφ (p m-p n)).mp
    rw [map_sub]
    exact sub_nonneg.mpr (hp.2.1 h)
  · intro g hg hgp
    obtain ⟨G,hG,hr⟩ := exists_state_extension_of_injective φ hφ g hg
    have he : G = F := hp.2.2.2.2 G hG (fun n => by
      change restrictState φ G (p n) = 1
      rw [hr]
      exact hgp n)
    rw [← hr,he]
  · intro G H hG hH hrG hrH
    exact (hn G hG hrG).trans (hn H hH hrH).symm

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (D : PeakingPairData A) (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ)
  (τ : C →ₚ[ℂ] ℂ) (htr : IsTracialPositive τ) (hn : τ 1 = 1)
  (hf : ∀ a, τ (star a*a) = 0 → a = 0)
  (ht : ∀ a, τ (φ a) = D.trace a)
  (hu : ∀ i, StateExtensionUnique φ (D.state i))

def pushedState (i : Bool) : C →L[ℂ] ℂ :=
  Classical.choose ((hu i).exists_unique_pure hφ (D.peaks i).isPureState)

theorem pushedState_isPure (i : Bool) : IsPureState (D.pushedState φ hφ hu i) :=
  (Classical.choose_spec ((hu i).exists_unique_pure hφ (D.peaks i).isPureState)).1

theorem pushedState_restrict (i : Bool) :
    restrictState φ (D.pushedState φ hφ hu i) = D.state i :=
  (Classical.choose_spec ((hu i).exists_unique_pure hφ (D.peaks i).isPureState)).2.1

def push : PeakingPairData C where
  trace := τ
  tracial := htr
  normalized := hn
  faithful := hf
  peak i n := φ (D.peak i n)
  state := D.pushedState φ hφ hu
  peaks i := (D.peaks i).extend φ (hu i) _ (D.pushedState_isPure φ hφ hu i).1
    (D.pushedState_restrict φ hφ hu i)
  peak_zero i := by rw [D.peak_zero,map_one]
  atom_positive i n := by
    change 0 < (τ (φ (D.peak i n)-φ (D.peak i (n+1)))).re
    rw [← map_sub,ht]
    exact D.atom_positive i n
  trace_null i := by
    simpa only [ht] using D.trace_null i
  matched i n := by rw [ht,ht,D.matched]

variable (B : PeakingPairData A)

def hnnPush (hs : B.Separated) (hA : IsSimpleCStar A)
    (htrace : ∀ a, B.trace a = D.trace a) : PeakingPairData B.HNNAlgebra :=
  D.push B.hnnBase B.hnnBase_injective
    (positiveOfSquares B.hnnTrace B.hnnTrace_isState.2) B.hnnTrace_tracial
    ((isState_iff B.hnnTrace).mp B.hnnTrace_isState).1 B.hnnTrace_faithful
    (fun a => (B.hnnTrace_base a).trans (htrace a)) (fun i => B.hnn_unique hs hA _ (D.peaks i).isPureState)

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem hnn_restriction {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) (hw : ∀ i, star (w i) = w (!i))
    (hr : ∀ i a, w i*ψ a*w (!i) = w i*ψ (B.turnCenter i a)*w (!i) +
      ψ (B.turnRemainder i a))
    (g : C →ₚ[ℂ] ℂ) (hg : ∀ c : C, g (star c*c) = 0 → c = 0)
    (hbase : ∀ a, g (ψ a) = B.trace a)
    (hred : ∀ (u : HNNWord A) a, u.Reduced B.turnCentered →
      g (ψ a*u.eval ψ w) = 0) :
    ∃ F : B.HNNAlgebra →⋆ₐ[ℂ] C, Function.Injective F ∧
      (∀ a, F (B.hnnBase a) = ψ a) ∧ (∀ i, F (B.hnnLetter i) = w i) ∧
      (∀ b, g (F b) = B.hnnTrace b) ∧ F.range = hnnGenerated ψ w := by
  apply exists_hnnRestriction B.hnnBase ψ B.hnnLetter w B.hnnLetter_star hw
    B.turnCentered B.turnCenter B.turnRemainder B.turnCenter_centered B.hnnLetter_turn hr
    (positiveOfSquares B.hnnTrace B.hnnTrace_isState.2) g
  · intro a
    exact (B.hnnTrace_base a).trans (hbase a).symm
  · intro u a hu
    change B.hnnTrace _ = g _
    rw [← B.hnnTrace_expectation,B.hnnExpectation_word u a hu,hred u a hu,map_zero]
  · exact B.hnnTrace_faithful
  · exact hg
  · exact B.hnn_generated

theorem hnn_restriction_expectation {C D : Type*} [CStarAlgebra C] [CStarAlgebra D]
    (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) (ι : A →⋆ₐ[ℂ] D)
    (F : B.HNNAlgebra →⋆ₐ[ℂ] C) (hbase : ∀ a, F (B.hnnBase a) = ψ a)
    (hletter : ∀ i, F (B.hnnLetter i) = w i)
    (G : C →L[ℂ] D) (hG : ∀ a, G (ψ a) = ι a)
    (hGr : ∀ (u : HNNWord A) a, u.Reduced B.turnCentered →
      G (ψ a*u.eval ψ w) = 0) (b : B.HNNAlgebra) :
    G (F b) = ι (B.hnnExpectation b) :=
  hnn_expectation_intertwines B.hnnBase ψ ι B.hnnLetter w F hbase hletter
    B.hnnLetter_star B.turnCentered B.turnCenter B.turnRemainder B.turnCenter_centered
    B.hnnLetter_turn B.hnnExpectation G B.hnnExpectation_base hG B.hnnExpectation_word hGr
    B.hnn_generated b

end PeakingPairData

section
namespace HNNWord
variable {A B C : Type*}

def lastCoefficient : HNNWord A → A
  | .single _ a => a
  | .cons _ _ w => w.lastCoefficient

def mapCoefficients (φ : A → B) : HNNWord A → HNNWord B
  | .single i a => .single i (φ a)
  | .cons i a w => .cons i (φ a) (w.mapCoefficients φ)

@[simp] theorem first_mapCoefficients (φ : A → B) (w : HNNWord A) :
    (w.mapCoefficients φ).first = w.first := by cases w <;> rfl

@[simp] theorem last_mapCoefficients (φ : A → B) (w : HNNWord A) :
    (w.mapCoefficients φ).lastCoefficient = φ w.lastCoefficient := by
  induction w with
  | single i a => rfl
  | cons i a w ih => exact ih

theorem mapCoefficients_reduced (φ : A → B) (K : Bool → A → Prop) (L : Bool → B → Prop)
    (h : ∀ i a, K i a → L i (φ a)) (w : HNNWord A) (hw : w.Reduced K) :
    (w.mapCoefficients φ).Reduced L := by
  induction w with
  | single i a => trivial
  | cons i a w ih =>
    exact ⟨hw.1.imp (fun hh => by simpa only [first_mapCoefficients] using hh) (h i a),ih hw.2⟩

theorem eval_mapCoefficients [Mul C] (φ : A → B) (ψ : B → C) (v : Bool → C)
    (w : HNNWord A) : (w.mapCoefficients φ).eval ψ v = w.eval (ψ ∘ φ) v := by
  induction w with
  | single i a => rfl
  | cons i a w ih => simp only [mapCoefficients,eval,ih]; rfl

def join [Mul B] : HNNWord B → B → HNNWord B → HNNWord B
  | .single i a, b, z => .cons i (a*b) z
  | .cons i a w, b, z => .cons i a (w.join b z)

@[simp] theorem first_join [Mul B] (w z : HNNWord B) (b : B) :
    (w.join b z).first = w.first := by cases w <;> rfl

@[simp] theorem last_join [Mul B] (w z : HNNWord B) (b : B) :
    (w.join b z).lastCoefficient = z.lastCoefficient := by
  induction w with
  | single i a => rfl
  | cons i a w ih => exact ih

theorem join_reduced [Mul B] (L : Bool → B → Prop) (w z : HNNWord B) (b : B)
    (hw : w.Reduced L) (hz : z.Reduced L) (hb : ∀ i, L i (w.lastCoefficient*b)) :
    (w.join b z).Reduced L := by
  induction w with
  | single i a => exact ⟨Or.inr (hb i),hz⟩
  | cons i a w ih =>
    exact ⟨by simpa only [first_join] using hw.1, ih hw.2 hb⟩

theorem eval_join [Monoid B] [Monoid C] (ψ : B →* C) (v : Bool → C)
    (w z : HNNWord B) (b : B) :
    (w.join b z).eval ψ v = w.eval ψ v * ψ b * z.eval ψ v := by
  induction w with
  | single i a => simp only [join,eval,map_mul,mul_assoc]
  | cons i a w ih => simp only [join,eval,ih,mul_assoc]
end HNNWord

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) (v : Bool → C)
  (K : Bool → A → Prop) (L : Bool → B → Prop)

def hnnBaseTailSpan : Submodule ℂ C := Submodule.span ℂ
  {x | ∃ (w : HNNWord B) (b : B), w.Reduced L ∧
    w.lastCoefficient ∈ Set.range φ ∧ x = ψ b*w.eval ψ v}

theorem hnnBaseTailSpan_contains_word
    (hKL : ∀ i a, K i a → L i (φ a)) (w : HNNWord A) (a : A) (hw : w.Reduced K) :
    (ψ.comp φ) a*w.eval (ψ.comp φ) v ∈ hnnBaseTailSpan φ ψ v L := by
  have he : (w.mapCoefficients φ).eval ψ v = w.eval (ψ.comp φ) v :=
    w.eval_mapCoefficients φ ψ v
  exact Submodule.subset_span ⟨w.mapCoefficients φ,φ a,
    w.mapCoefficients_reduced φ K L hKL hw,
    ⟨w.lastCoefficient,w.last_mapCoefficients φ |>.symm⟩,by rw [he]; rfl⟩

theorem hnnBaseTailSpan_mul_center_word
    (hKL : ∀ i a, K i a → L i (φ a))
    (b : B) (hb : ∀ i a c, L i (φ a*b*φ c))
    (z : HNNWord A) (a : A) (hz : z.Reduced K)
    {x : C} (hx : x ∈ hnnBaseTailSpan φ ψ v L) :
    x*ψ b*((ψ.comp φ) a*z.eval (ψ.comp φ) v) ∈ hnnBaseTailSpan φ ψ v L := by
  have hze : (z.mapCoefficients φ).eval ψ v = z.eval (ψ.comp φ) v :=
    z.eval_mapCoefficients φ ψ v
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,c,hw,⟨d,hd⟩,rfl⟩ := hx
    have hjoin := w.join_reduced L (z.mapCoefficients φ) (b*φ a) hw
      (z.mapCoefficients_reduced φ K L hKL hz) (fun i => by
        rw [← hd,← mul_assoc]; exact hb i d a)
    apply Submodule.subset_span
    refine ⟨w.join (b*φ a) (z.mapCoefficients φ),c,hjoin,?_,?_⟩
    · rw [HNNWord.last_join,HNNWord.last_mapCoefficients]
      exact ⟨z.lastCoefficient,rfl⟩
    · have heval : (w.join (b*φ a) (z.mapCoefficients φ)).eval ψ v =
          w.eval ψ v * ψ (b*φ a) * (z.mapCoefficients φ).eval ψ v :=
        w.eval_join ψ.toMonoidHom v (z.mapCoefficients φ) (b*φ a)
      rw [heval,hze]
      simp only [map_mul,StarAlgHom.comp_apply,mul_assoc]
  | zero => simpa only [zero_mul] using (hnnBaseTailSpan φ ψ v L).zero_mem
  | add x y hx hy ix iy =>
    simpa only [add_mul] using (hnnBaseTailSpan φ ψ v L).add_mem ix iy
  | smul c x hx ix =>
    simpa only [smul_mul_assoc] using (hnnBaseTailSpan φ ψ v L).smul_mem c ix

end

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C)

theorem hnn_inclusion (ι : A →⋆ₐ[ℂ] C)
    (htrace : ∀ a, D.trace (ι a) = B.trace a)
    (hdiag : ∀ i a, ι (B.diagonal i a) = D.diagonal i a)
    (hexpect : ∀ i a, (D.input false).expectation i (ι a) =
      (B.input false).expectation i a) :
    ∃ F : B.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra, Function.Injective F ∧
      (∀ a, F (B.hnnBase a) = D.hnnBase (ι a)) ∧
      (∀ i, F (B.hnnLetter i) = D.hnnLetter i) ∧
      (∀ b, D.hnnTrace (F b) = B.hnnTrace b) ∧
      F.range = hnnGenerated (D.hnnBase.comp ι) D.hnnLetter ∧
      (∀ b, D.hnnExpectation (F b) = ι (B.hnnExpectation b)) := by
  have hc (i : Bool) (a : A) : ι (B.turnCenter i a) = D.turnCenter i (ι a) := by
    simp only [turnCenter,map_sub,hdiag,hexpect]
  have hr (i : Bool) (a : A) : ι (B.turnRemainder i a) = D.turnRemainder i (ι a) := by
    simp only [turnRemainder,hdiag,hexpect]
  have hturn i a : D.hnnLetter i*(D.hnnBase.comp ι) a*D.hnnLetter (!i) =
      D.hnnLetter i*(D.hnnBase.comp ι) (B.turnCenter i a)*D.hnnLetter (!i) +
      (D.hnnBase.comp ι) (B.turnRemainder i a) := by
    simp only [StarAlgHom.comp_apply,hc,hr]
    exact D.hnnLetter_turn i (ι a)
  have hK i a (ha : B.turnCentered i a) : D.turnCentered i (ι a) := by
    change (D.input false).expectation (!i) (ι a) = 0
    rw [hexpect]
    exact ha
  have hzero (u : HNNWord A) (a : A) (hu : u.Reduced B.turnCentered) :
      D.hnnExpectation ((D.hnnBase.comp ι) a*u.eval (D.hnnBase.comp ι) D.hnnLetter) = 0 := by
    have hv := HNNWord.mapCoefficients_reduced ι B.turnCentered D.turnCentered hK u hu
    have he : (u.mapCoefficients ι).eval D.hnnBase D.hnnLetter =
      u.eval (D.hnnBase.comp ι) D.hnnLetter :=
      u.eval_mapCoefficients ι D.hnnBase D.hnnLetter
    simpa only [he,StarAlgHom.comp_apply] using D.hnnExpectation_word (u.mapCoefficients ι) (ι a) hv
  obtain ⟨F,hF,hFa,hFv,hFt,hFr⟩ := B.hnn_restriction (D.hnnBase.comp ι) D.hnnLetter
    D.hnnLetter_star hturn (positiveOfSquares D.hnnTrace D.hnnTrace_isState.2)
    D.hnnTrace_faithful
    (fun a => (D.hnnTrace_base (ι a)).trans (htrace a))
    (fun u a hu => by
      change D.hnnTrace _ = 0
      rw [← D.hnnTrace_expectation,hzero u a hu,map_zero])
  refine ⟨F,hF,hFa,hFv,hFt,hFr,?_⟩
  exact fun b => B.hnn_restriction_expectation (D.hnnBase.comp ι) D.hnnLetter ι F hFa hFv
    D.hnnExpectation (fun a => D.hnnExpectation_base (ι a)) hzero b

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C)

theorem peakAtom_separates (i : Bool) (a b : A)
    (h : ∀ n, peakAtom (B.peak i) n*a = peakAtom (B.peak i) n*b) : a = b :=
  ((B.input false).data i).separating a b h

theorem diagonal_atom (i : Bool) (g : SequenceDiagonal) (n : ℕ) :
    peakAtom (B.peak i) n*B.diagonal i g = g n • peakAtom (B.peak i) n :=
  (B.input false).atom_mul i g n

theorem expectation_nat (i : Bool) (a : A) (n : ℕ) :
    (B.input false).expectation i a n =
      (B.trace (peakAtom (B.peak i) n)).re⁻¹ •
        B.trace (peakAtom (B.peak i) n*a*peakAtom (B.peak i) n) := rfl

theorem expectation_infty (i : Bool) (a : A) :
    (B.input false).expectation i a ∞ = B.state i a := rfl

variable (ι : A →⋆ₐ[ℂ] C) (hp : ∀ i n, ι (B.peak i n) = D.peak i n)

include hp in
theorem atom_natural (i : Bool) (n : ℕ) :
    ι (peakAtom (B.peak i) n) = peakAtom (D.peak i) n := by
  simp only [peakAtom,map_sub,hp]

include hp in
theorem state_natural (i : Bool) : restrictState ι (D.state i) = B.state i := by
  apply (B.peaks i).2.2.2.2 _ (isState_restrict ι _ (D.peaks i).2.2.1)
  intro n
  change D.state i (ι (B.peak i n)) = 1
  rw [hp]
  exact (D.peaks i).2.2.2.1 n

include hp in
theorem diagonal_natural (i : Bool) (g : SequenceDiagonal) :
    ι (B.diagonal i g) = D.diagonal i g := by
  apply D.peakAtom_separates i
  intro n
  rw [← B.atom_natural D ι hp i n,← map_mul,B.diagonal_atom,map_smul,
    B.atom_natural D ι hp,D.diagonal_atom]

include hp in
theorem expectation_natural (ht : ∀ a, D.trace (ι a) = B.trace a) (i : Bool) (a : A) :
    (D.input false).expectation i (ι a) = (B.input false).expectation i a := by
  ext x
  induction x using OnePoint.rec with
  | infty =>
    rw [D.expectation_infty,B.expectation_infty]
    exact congrArg (fun f : A →L[ℂ] ℂ => f a) (B.state_natural D ι hp i)
  | coe n =>
    rw [D.expectation_nat,B.expectation_nat,← B.atom_natural D ι hp i n,
      ← map_mul,← map_mul,ht,ht]

include hp in

theorem hnn_inclusion_of_peaks (ht : ∀ a, D.trace (ι a) = B.trace a) :
    ∃ F : B.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra, Function.Injective F ∧
      (∀ a, F (B.hnnBase a) = D.hnnBase (ι a)) ∧
      (∀ i, F (B.hnnLetter i) = D.hnnLetter i) ∧
      (∀ b, D.hnnTrace (F b) = B.hnnTrace b) ∧
      F.range = hnnGenerated (D.hnnBase.comp ι) D.hnnLetter ∧
      (∀ b, D.hnnExpectation (F b) = ι (B.hnnExpectation b)) :=
  B.hnn_inclusion D ι ht (B.diagonal_natural D ι hp) (B.expectation_natural D ι hp ht)

end PeakingPairData

open Topology
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C)

theorem hnn_equiv_of_peaks (e : A ≃⋆ₐ[ℂ] C)
    (hp : ∀ i n, e (B.peak i n) = D.peak i n)
    (ht : ∀ a, D.trace (e a) = B.trace a) :
    ∃ E : B.HNNAlgebra ≃⋆ₐ[ℂ] D.HNNAlgebra,
      (∀ a, E (B.hnnBase a) = D.hnnBase (e a)) ∧
      (∀ i, E (B.hnnLetter i) = D.hnnLetter i) ∧
      (∀ b, D.hnnTrace (E b) = B.hnnTrace b) ∧
      (∀ b, D.hnnExpectation (E b) = e (B.hnnExpectation b)) := by
  obtain ⟨F,hF,hb,hv,htr,hr,he⟩ := B.hnn_inclusion_of_peaks D e.toStarAlgHom hp ht
  have hbr : Set.range (D.hnnBase.comp e.toStarAlgHom) = Set.range D.hnnBase := by
    apply Set.Subset.antisymm
    · rintro _ ⟨a,rfl⟩
      exact ⟨e a,rfl⟩
    · rintro _ ⟨c,rfl⟩
      obtain ⟨a,rfl⟩ := e.surjective c
      exact ⟨a,rfl⟩
  have hs : Function.Surjective F := by
    intro x
    have hx : x ∈ hnnGenerated (D.hnnBase.comp e.toStarAlgHom) D.hnnLetter := by
      change x ∈ closure (StarAlgebra.adjoin ℂ
        (Set.range (D.hnnBase.comp e.toStarAlgHom) ∪ Set.range D.hnnLetter) : Set D.HNNAlgebra)
      rw [hbr]
      exact D.hnn_generated x
    rw [← hr] at hx
    exact hx
  exact ⟨StarAlgEquiv.ofBijective F ⟨hF,hs⟩,hb,hv,htr,he⟩

end PeakingPairData

end NaimarkZFC

end

end OAI
