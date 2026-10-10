import OAI.Algebra.Determinantal.Normalization

namespace OAI

namespace PermanentBorder.Conductor
section Coordinate
variable {O L ι : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
  [Field L] [Algebra O L] [IsFractionRing O L] [Finite ι]

theorem principal_coordinate (w : ι → L) (hw : ∃ i, w i ≠ 0) :
    ∃ g : L, g ≠ 0 ∧ ∃ c : ι → O,
      (∀ i, w i = algebraMap O L (c i) * g) ∧ Ideal.span (Set.range c) = ⊤ := by
  classical
  let M := Submodule.span O (Set.range w)
  have hfg : M.FG := Submodule.fg_span (Set.finite_range w)
  let I : FractionalIdeal (nonZeroDivisors O) L :=
    ⟨M, FractionalIdeal.isFractional_of_fg hfg⟩
  have : M.IsPrincipal := FractionalIdeal.isPrincipal I
  let g := Submodule.IsPrincipal.generator M
  have hg : g ≠ 0 := by
    intro hz
    have hm : M = ⊥ := (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero M).mpr hz
    obtain ⟨i, hi⟩ := hw
    apply hi
    have hwi : w i ∈ M := Submodule.subset_span (Set.mem_range_self i)
    simpa [hm] using hwi
  have hc (i : ι) : ∃ c : O, w i = c • g :=
    (Submodule.IsPrincipal.mem_iff_eq_smul_generator M).mp
      (Submodule.subset_span (Set.mem_range_self i))
  choose c hc using hc
  refine ⟨g, hg, c, (fun i => by simpa [Algebra.smul_def] using hc i), ?_⟩
  let J := Ideal.span (Set.range c)
  have hrep (x : L) (hx : x ∈ M) : ∃ a : O, a ∈ J ∧ x = a • g := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨c i, Ideal.subset_span (Set.mem_range_self i), hc i⟩
    | zero => exact ⟨0, J.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, J.add_mem ha hb, (add_smul _ _ _).symm⟩
    | smul a x _ hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      exact ⟨a * b, J.mul_mem_left a hb, (mul_smul _ _ _).symm⟩
  obtain ⟨a, ha, he⟩ := hrep g (Submodule.IsPrincipal.generator_mem M)
  have he' : algebraMap O L a = 1 := by
    apply (mul_right_inj' hg).mp
    simpa [Algebra.smul_def, mul_comm] using he.symm
  have ha1 : a = 1 := (IsFractionRing.injective O L) (by simpa using he')
  exact Ideal.eq_top_of_isUnit_mem J (ha1 ▸ ha) isUnit_one
end Coordinate

open scoped BigOperators
section GenericCombination
variable {K O ι γ : Type*} [Field K] [Infinite K] [CommRing O] [Algebra K O]
  [Fintype ι] [Finite γ] [Finite (MaximalSpectrum O)]

theorem simultaneous_unit_combination (v : γ → ι → O)
    (hv : ∀ j, Ideal.span (Set.range (v j)) = ⊤) :
    ∃ a : ι → K, ∀ j, IsUnit (∑ i, algebraMap K O (a i) * v j i) := by
  classical
  let ℓ (j : γ) : (ι → K) →ₗ[K] O :=
    { toFun := fun a => ∑ i, a i • v j i
      map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c a; simp [smul_smul, Finset.smul_sum] }
  let p (j : γ × MaximalSpectrum O) : Submodule K (ι → K) :=
    (j.2.asIdeal.restrictScalars K).comap (ℓ j.1)
  have hp (j : γ × MaximalSpectrum O) : p j ≠ ⊤ := by
    intro h
    have hm : Ideal.span (Set.range (v j.1)) ≤ j.2.asIdeal := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have ht : Pi.single i (1 : K) ∈ p j := by rw [h]; trivial
      change (∑ t, (Pi.single i (1 : K) : ι → K) t • v j.1 t) ∈ j.2.asIdeal at ht
      simpa using ht
    rw [hv] at hm
    exact j.2.isMaximal.ne_top (top_le_iff.mp hm)
  obtain ⟨a, ha⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨a, fun j => ?_⟩
  by_contra hu
  obtain ⟨M, hM, hvM⟩ := exists_max_ideal_of_mem_nonunits hu
  exact ha (j, ⟨M, hM⟩) (by simpa only [p, Submodule.mem_comap,
    Submodule.restrictScalars_mem, LinearMap.coe_mk, AddHom.coe_mk, ℓ,
    Algebra.smul_def] using hvM)
end GenericCombination

section Ratios
variable {K O L ι γ : Type*} [Field K] [Infinite K]
  [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra K O]
  [Field L] [Algebra O L] [IsFractionRing O L] [Algebra K L] [IsScalarTower K O L]
  [Fintype ι] [Finite γ] [Finite (MaximalSpectrum O)]

theorem simultaneous_coordinate_generator (w : ι → γ → L)
    (hw : ∀ j, ∃ i, w i j ≠ 0) :
    ∃ a : ι → K,
      (∀ j, (∑ i, algebraMap K L (a i) * w i j) ≠ 0) ∧
      ∀ i j, ∃ c : O, w i j = algebraMap O L c *
        (∑ t, algebraMap K L (a t) * w t j) := by
  classical
  choose g hg c hc hspan using fun j => principal_coordinate (O := O) (fun i => w i j) (hw j)
  obtain ⟨a, ha⟩ := simultaneous_unit_combination (K := K) c hspan
  let u (j : γ) : Oˣ := (ha j).unit
  have hu (j : γ) : (u j : O) = ∑ i, algebraMap K O (a i) * c j i := (ha j).unit_spec
  have hh (j : γ) : (∑ i, algebraMap K L (a i) * w i j) =
      algebraMap O L (u j) * g j := by
    rw [hu, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, ← IsScalarTower.algebraMap_apply K O L, hc]
    ring
  refine ⟨a, fun j => ?_, fun i j => ?_⟩
  · rw [hh]
    exact mul_ne_zero ((u j).isUnit.map (algebraMap O L)).ne_zero (hg j)
  · refine ⟨c j i * ↑(u j)⁻¹, ?_⟩
    rw [hh, hc, map_mul]
    have hi : algebraMap O L (↑(u j)⁻¹ : O) * algebraMap O L (u j) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc
      algebraMap O L (c j i) * g j =
          algebraMap O L (c j i) * (1 * g j) := by rw [one_mul]
      _ = _ := by rw [← hi]; ring
end Ratios
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
section Coordinates
variable {S A L γ : Type*} [CommRing S] [CommRing A] [Field L]
  [Algebra S A] [Algebra S L] [Finite γ]
  [Module.Finite S (integralClosure S L)]

theorem isIntegral_of_coordinates (f : A →ₐ[S] (γ → L))
    (hf : Function.Injective f) {x : A} (hx : ∀ j, IsIntegral S (f x j)) :
    IsIntegral S x := by
  let z : γ → integralClosure S L := fun j => ⟨f x j, hx j⟩
  let ρ : (γ → integralClosure S L) →ₐ[S] (γ → L) :=
    AlgHom.pi fun j => (integralClosure S L).val.comp
      (Pi.evalAlgHom S (fun _ : γ => integralClosure S L) j)
  have hz : IsIntegral S z := Algebra.IsIntegral.isIntegral z
  have hr : ρ z = f x := rfl
  exact (isIntegral_algHom_iff f hf).mp (hr ▸ hz.map ρ)
end Coordinates

section UnitCoordinates
variable {Q A L γ : Type*} [Field Q] [CommRing A] [Field L]
  [Algebra Q A] [Algebra Q L] [Module.Finite Q A]

theorem isUnit_of_coordinates (f : A →ₐ[Q] (γ → L))
    (hf : Function.Injective f) {x : A} (hx : ∀ j, f x j ≠ 0) : IsUnit x := by
  have : IsArtinianRing A := IsArtinianRing.of_finite Q A
  apply IsArtinianRing.isUnit_of_mem_nonZeroDivisors
  rw [mem_nonZeroDivisors_iff_right]
  intro z hz
  apply hf
  ext j
  have h := congrFun (congrArg f hz) j
  simpa only [map_mul, map_zero, Pi.mul_apply, Pi.zero_apply,
    mul_eq_zero, hx j, or_false] using h
end UnitCoordinates
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open scoped BigOperators
section NormalizedLattice
variable {K S Q A L ι γ : Type*} [Field K] [Infinite K]
  [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [IsLocalRing S] [Algebra K S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
  [CommRing A] [Algebra Q A] [Algebra S A] [IsScalarTower S Q A]
  [Field L] [Algebra Q L] [Algebra S L] [IsScalarTower S Q L]
  [Algebra K L] [IsScalarTower K S L]
  [Module.Finite Q A] [FiniteDimensional Q L] [Algebra.IsSeparable Q L]
  [Fintype ι] [Finite γ]

include K in

theorem exists_normalizing_lattice_element (f : A →ₐ[Q] (γ → L))
    (hf : Function.Injective f) (l : ι → A)
    (hl : ∀ j, ∃ i, f (l i) j ≠ 0) :
    ∃ u : Aˣ, (u : A) ∈ Submodule.span S (Set.range l) ∧
      ∀ x ∈ Submodule.span S (Set.range l), IsIntegral S ((↑u⁻¹ : A) * x) := by
  classical
  let O := integralClosure S L
  have : Module.Finite S O := IsIntegralClosure.finite S Q L O
  have : IsPrincipalIdealRing O := integralClosure_isPrincipalIdealRing (Q := Q)
  have : Finite (MaximalSpectrum O) := finite_maximalSpectrum_of_finite_local (S := S)
  have : IsFractionRing O L := IsIntegralClosure.isFractionRing_of_finite_extension S Q L O
  let : Algebra K O := ((integralClosure S L).restrictScalars K).algebra
  have : IsScalarTower K O L := IsScalarTower.of_algebraMap_eq fun x => rfl
  obtain ⟨a, ha, hrat⟩ := simultaneous_coordinate_generator (K := K) (O := O)
    (fun i j => f (l i) j) hl
  let h : A := ∑ i, algebraMap K S (a i) • l i
  have hh (j : γ) : f h j = ∑ i, algebraMap K L (a i) * f (l i) j := by
    change (f.restrictScalars S) h j = _
    simp [h, Algebra.smul_def, ← IsScalarTower.algebraMap_apply K S L]
  have hu : IsUnit h := isUnit_of_coordinates f hf (fun j => hh j ▸ ha j)
  let u := hu.unit
  have huval : (u : A) = h := hu.unit_spec
  have hmem : h ∈ Submodule.span S (Set.range l) := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  refine ⟨u, huval.symm ▸ hmem, ?_⟩
  have hli (i : ι) : IsIntegral S ((↑u⁻¹ : A) * l i) := by
    apply isIntegral_of_coordinates (f.restrictScalars S) hf
    intro j
    obtain ⟨c, hc⟩ := hrat i j
    have he : f ((↑u⁻¹ : A) * l i) j = algebraMap O L c := by
      rw [map_mul, Pi.mul_apply, hc, ← hh j, ← huval]
      have hinv : f (↑u⁻¹ : A) j * f (u : A) j = 1 := by
        have hi := congrFun (congrArg f (Units.inv_mul u)) j
        simpa only [map_mul, map_one, Pi.mul_apply, Pi.one_apply] using hi
      calc
        f (↑u⁻¹ : A) j * (algebraMap O L c * f (u : A) j) =
          algebraMap O L c * (f (↑u⁻¹ : A) j * f (u : A) j) := by ring
        _ = algebraMap O L c := by rw [hinv, mul_one]
    change IsIntegral S (f ((↑u⁻¹ : A) * l i) j)
    rw [he]
    exact c.property
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hli i
  | zero => simpa using (isIntegral_zero : IsIntegral S (0 : A))
  | add x y _ _ hx hy => simpa only [mul_add] using hx.add hy
  | smul s x _ hx =>
    simpa only [mul_smul_comm] using hx.smul s
end NormalizedLattice
end PermanentBorder.Conductor
namespace PermanentBorder.Conductor
open Polynomial Matrix Module
section MatrixGenerators
variable {K S Q ι : Type*} [Field K] [Infinite K]
  [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [IsLocalRing S] [Algebra K S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]
  [Fintype ι] [DecidableEq ι]

include K in

theorem exists_normalizing_matrix_generators (T : Matrix ι ι S)
    (hsep : (T.charpoly.map (algebraMap S Q)).Separable) :
    ∃ (l : ι → AdjoinRoot (T.charpoly.map (algebraMap S Q)))
      (u : (AdjoinRoot (T.charpoly.map (algebraMap S Q)))ˣ),
      (∀ j, genericBaseChange (Q := Q) T.charpoly (AdjoinRoot.root T.charpoly) * l j =
        ∑ i, algebraMap S (AdjoinRoot (T.charpoly.map (algebraMap S Q))) (T i j) * l i) ∧
      (u : AdjoinRoot (T.charpoly.map (algebraMap S Q))) ∈
        Submodule.span S (Set.range l) ∧
      ∀ x ∈ Submodule.span S (Set.range l), IsIntegral S ((↑u⁻¹) * x) := by
  classical
  let : Algebra K Q := ((algebraMap S Q).comp (algebraMap K S)).toAlgebra
  let : IsScalarTower K S Q := IsScalarTower.of_algebraMap_eq fun x => rfl
  have : Infinite Q := Infinite.of_injective (algebraMap K Q) (algebraMap K Q).injective
  let f := T.charpoly.map (algebraMap S Q)
  let A := AdjoinRoot f
  let L := f.SplittingField
  have : IsScalarTower K S L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K Q L, IsScalarTower.algebraMap_apply S Q L,
      IsScalarTower.algebraMap_apply K S Q]
  have : Module.Finite Q A := (T.charpoly_monic.map _).finite_adjoinRoot
  have : Algebra.IsSeparable Q L := Algebra.isSeparable_of_separable_splitting_field Q L hsep
  obtain ⟨e, he⟩ : ∃ e : (ι → Q) ≃ₗ[Q] A,
      ∀ x, e ((T.map (algebraMap S Q)) *ᵥ x) = AdjoinRoot.root f * e x := by
    have hs : (T.map (algebraMap S Q)).charpoly.Separable := by
      simpa only [charpoly_map] using hsep
    obtain ⟨e₀, he₀⟩ := exists_generic_matrix_equiv (T.map (algebraMap S Q)) hs
    let a := AdjoinRoot.algEquivOfEq Q (T.map (algebraMap S Q)).charpoly f
      (charpoly_map T (algebraMap S Q))
    refine ⟨e₀.trans a.toLinearEquiv, fun x => ?_⟩
    change a (e₀ _) = AdjoinRoot.root f * a (e₀ x)
    rw [he₀, map_mul, show a (AdjoinRoot.root (T.map (algebraMap S Q)).charpoly) =
      AdjoinRoot.root f from AdjoinRoot.algEquivOfEq_root (R := Q) _ _ _]
  let l : ι → A := fun i => e (Pi.single i 1)
  have hsum (x : ι → Q) : e x = ∑ i, x i • l i := by
    have hx : x = ∑ i, x i • Pi.single i (1 : Q) := by
      ext j; simp [Pi.single_apply]
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, l]
  have hl (j : f.rootSet L) : ∃ i, rootEvaluation (f := f) (L := L) (l i) j ≠ 0 := by
    by_contra hn
    push Not at hn
    have h := congrFun (congrArg (rootEvaluation (f := f) (L := L)) (hsum (e.symm 1))) j
    rw [e.apply_symm_apply] at h
    simp [hn] at h
  obtain ⟨u, hu, hnorm⟩ := exists_normalizing_lattice_element (K := K) (S := S)
    (rootEvaluation (f := f) (L := L))
    (rootEvaluation_injective (T.charpoly_monic.map _) hsep (SplittingField.splits f)) l hl
  refine ⟨l, u, ?_, hu, hnorm⟩
  intro j
  have hg : genericBaseChange (Q := Q) T.charpoly (AdjoinRoot.root T.charpoly) =
      AdjoinRoot.root f := by
    simpa only [AdjoinRoot.root, Polynomial.map_X] using
      genericBaseChange_mk (Q := Q) T.charpoly X
  rw [hg, ← he, hsum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
    Matrix.map_apply, Algebra.smul_def, ← IsScalarTower.algebraMap_apply S Q A]
  rfl
end MatrixGenerators
end PermanentBorder.Conductor

namespace PermanentBorder.Conductor
open Matrix Polynomial

section MatrixFactorization
variable {R ι : Type*} [CommRing R] [IsDomain R]
  [Fintype ι] [DecidableEq ι]

abbrev DetQuotient (M : Matrix ι ι R) := R ⧸ Ideal.span {M.det}

theorem kernel_eq_adjugate_image (M : Matrix ι ι R) (hM : M.det ≠ 0)
    (v : ι → DetQuotient M) :
    (M.map (Ideal.Quotient.mk (Ideal.span {M.det}))) *ᵥ v = 0 ↔
      ∃ w : ι → DetQuotient M,
        (M.adjugate.map (Ideal.Quotient.mk (Ideal.span {M.det}))) *ᵥ w = v := by
  classical
  let π : R →+* DetQuotient M := Ideal.Quotient.mk _
  constructor
  · intro hv
    change (M.map π) *ᵥ v = 0 at hv
    obtain ⟨b, hb⟩ : ∃ b : ι → R, ∀ i, π (b i) = v i := by
      choose b hb using (fun i => Ideal.Quotient.mk_surjective (v i))
      exact ⟨b, hb⟩
    have hdiv (i : ι) : M.det ∣ (M *ᵥ b) i := by
      apply Ideal.mem_span_singleton.mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hm := π.map_mulVec M b i
      rw [show (π ∘ b) = v by funext j; exact hb j] at hm
      simpa only [hv, Pi.zero_apply, Function.comp_apply] using hm
    choose c hc using hdiv
    have hMc : M *ᵥ b = M.det • c := by funext i; exact hc i
    have hid : M.det • b = M.det • (M.adjugate *ᵥ c) := by
      calc
        M.det • b = M.adjugate *ᵥ (M *ᵥ b) := by
          rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
        _ = M.det • (M.adjugate *ᵥ c) := by rw [hMc, mulVec_smul]
    have hb' : M.adjugate *ᵥ c = b := by
      funext i
      exact (mul_left_cancel₀ hM (congrFun hid i)).symm
    refine ⟨π ∘ c, ?_⟩
    funext i
    change (M.adjugate.map π *ᵥ (π ∘ c)) i = v i
    rw [← π.map_mulVec, hb']
    exact hb i
  · rintro ⟨w, rfl⟩
    change (M.map π) *ᵥ ((M.adjugate.map π) *ᵥ w) = 0
    rw [mulVec_mulVec, ← Matrix.map_mul, mul_adjugate]
    have hd : π M.det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton M.det))
    have hz : (M.det • (1 : Matrix ι ι R)).map π = 0 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hd, zero_mul,
        Matrix.zero_apply]
    rw [hz, zero_mulVec]

theorem row_kernel_eq_adjugate_image (M : Matrix ι ι R) (hM : M.det ≠ 0)
    (v : ι → DetQuotient M) :
    v ᵥ* (M.map (Ideal.Quotient.mk (Ideal.span {M.det}))) = 0 ↔
      ∃ w : ι → DetQuotient M,
        w ᵥ* (M.adjugate.map (Ideal.Quotient.mk (Ideal.span {M.det}))) = v := by
  have ht := kernel_eq_adjugate_image Mᵀ (by simpa using hM)
  dsimp only [DetQuotient] at ht
  rw [det_transpose] at ht
  simp only [← adjugate_transpose, Matrix.transpose_map, mulVec_transpose] at ht
  exact ht v

end MatrixFactorization

end PermanentBorder.Conductor
namespace PermanentBorder.Conductor
open Matrix Polynomial
section
variable {S ι A : Type*} [CommRing S] [IsDomain S]
  [Fintype ι] [DecidableEq ι] [CommRing A] [Algebra S A]

def matrixEntryIdeal {B : Type*} [CommRing B] (N : Matrix ι ι B) : Ideal B :=
  Ideal.span (Set.range (fun ij : ι × ι => N ij.1 ij.2))

omit [Fintype ι] [DecidableEq ι] in
theorem entry_mem_matrixEntryIdeal {B : Type*} [CommRing B]
    (N : Matrix ι ι B) (i j : ι) : N i j ∈ matrixEntryIdeal N :=
  Ideal.subset_span ⟨(i,j), rfl⟩

omit [IsDomain S] in
theorem mapped_charmatrix (T : Matrix ι ι S) :
    T.charmatrix.map (AdjoinRoot.mk T.charpoly) =
      Matrix.scalar ι (AdjoinRoot.root T.charpoly) -
        T.map (algebraMap S (AdjoinRoot T.charpoly)) := by
  ext i j
  simp only [charmatrix, Matrix.map_apply, Matrix.sub_apply, map_sub,
    Matrix.scalar_apply, Matrix.diagonal_apply, AdjoinRoot.root]
  split_ifs <;> rfl

theorem conductor_mem_adjugate_of_lattice (T : Matrix ι ι S)
    (g : AdjoinRoot T.charpoly →ₐ[S] A) (hg : Function.Injective g)
    (l : ι → A)
    (hl : ∀ j, g (AdjoinRoot.root T.charpoly) * l j =
      ∑ i, algebraMap S A (T i j) * l i)
    (u : Aˣ) (hu : (u : A) ∈ Submodule.span S (Set.range l))
    (hnorm : ∀ x ∈ Submodule.span S (Set.range l), IsIntegral S ((↑u⁻¹ : A) * x))
    (a : AdjoinRoot T.charpoly)
    (ha : ∀ x : A, IsIntegral S x → ∃ b : AdjoinRoot T.charpoly,
      g b = g a * x) :
    a ∈ matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)) := by
  classical
  have hex (i : ι) : ∃ r : AdjoinRoot T.charpoly,
      g r = g a * ((↑u⁻¹ : A) * l i) :=
    ha _ (hnorm _ (Submodule.subset_span ⟨i, rfl⟩))
  choose r hr using hex
  have hrow : r ᵥ* T.charmatrix.map (AdjoinRoot.mk T.charpoly) = 0 := by
    rw [mapped_charmatrix, vecMul_sub]
    apply sub_eq_zero.mpr
    ext j
    simp only [scalar_apply]
    rw [vecMul_diagonal]
    simp only [vecMul, dotProduct]
    apply hg
    simp only [map_mul, map_sum, hr, AlgHom.commutes, Matrix.map_apply]
    calc
      (g a * ((↑u⁻¹ : A) * l j)) * g (AdjoinRoot.root T.charpoly) =
          (g a * (↑u⁻¹ : A)) * (g (AdjoinRoot.root T.charpoly) * l j) := by ring
      _ = (g a * (↑u⁻¹ : A)) * ∑ i, algebraMap S A (T i j) * l i := by rw [hl]
      _ = ∑ i, (g a * ((↑u⁻¹ : A) * l i)) * algebraMap S A (T i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  obtain ⟨w, hw⟩ := (row_kernel_eq_adjugate_image T.charmatrix T.charpoly_monic.ne_zero r).mp hrow
  have hrmem (j : ι) : r j ∈
      matrixEntryIdeal (T.charmatrix.adjugate.map (AdjoinRoot.mk T.charpoly)) := by
    rw [← hw]
    exact Ideal.sum_mem _ (fun i _ =>
      Ideal.mul_mem_left _ (w i) (entry_mem_matrixEntryIdeal _ i j))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hu
  have hae : a = ∑ i, algebraMap S (AdjoinRoot T.charpoly) (c i) * r i := by
    apply hg
    simp only [map_sum, map_mul, AlgHom.commutes, hr]
    have hc' : ∑ i, algebraMap S A (c i) * l i = (u : A) := by
      simpa only [Algebra.smul_def] using hc
    calc
      g a = (g a * (↑u⁻¹ : A)) * (u : A) := by simp [mul_assoc]
      _ = (g a * (↑u⁻¹ : A)) * ∑ i, algebraMap S A (c i) * l i := by rw [hc']
      _ = ∑ i, algebraMap S A (c i) * (g a * ((↑u⁻¹ : A) * l i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [hae]
  exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (hrmem i))
end
end PermanentBorder.Conductor

end OAI
