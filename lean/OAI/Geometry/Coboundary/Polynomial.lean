import OAI.Geometry.Coboundary.Lattices

namespace OAI

/-!
Polynomial-vector leading terms, degree reduction, and normalized rational lattice representatives.
-/

noncomputable section
open scoped Polynomial BigOperators

namespace CoboundaryExpanders.PolynomialVectors
variable {K : Type} [Field K] {N : ℕ}
abbrev V (K : Type) (N : ℕ) [Field K] := Fin N → K[X]

def Leading (v : V K N) (i : Fin N) (a : ℕ) : Prop :=
  (v i).coeff a ≠ 0 ∧ ∀ j b, N*a+i.val < N*b+j.val → (v j).coeff b = 0

lemma leading_ne_zero {v : V K N} {i : Fin N} {a : ℕ} (h : Leading v i a) : v ≠ 0 := by
  intro hv
  subst v
  simpa using h.1

lemma weight_injective {i j : Fin N} {a b : ℕ}
    (h : N*a+i.val = N*b+j.val) : i = j ∧ a = b := by
  have he : i.val = j.val := by
    have hh := congrArg (fun x => x % N) h
    simpa [Nat.add_mod,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using hh
  refine ⟨Fin.ext he,?_⟩
  have hm : N*a = N*b := by omega
  exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt i.isLt) hm

lemma leading_unique {v : V K N} {i j : Fin N} {a b : ℕ}
    (hi : Leading v i a) (hj : Leading v j b) : i = j ∧ a = b := by
  apply weight_injective
  apply le_antisymm
  · by_contra h
    exact hi.1 (hj.2 i a (by omega))
  · by_contra h
    exact hj.1 (hi.2 j b (by omega))

lemma exists_leading {v : V K N} (hv : v ≠ 0) : ∃ i a, Leading v i a := by
  classical
  let s : Finset ℕ := Finset.univ.biUnion fun i : Fin N =>
    (v i).support.image (fun a => N*a+i.val)
  have hs : s.Nonempty := by
    obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    obtain ⟨a,ha⟩ := Polynomial.support_nonempty.mpr hi
    refine ⟨N*a+i.val,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,?_⟩⟩
    exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  have hm := Finset.max'_mem s hs
  obtain ⟨i,_,ha⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp ha
  refine ⟨i,a,Polynomial.mem_support_iff.mp ha,?_⟩
  intro j b hb
  by_contra hn
  have hb' : N*b+j.val ∈ s := Finset.mem_biUnion.mpr
    ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨b,Polynomial.mem_support_iff.mpr hn,rfl⟩⟩
  have hh := Finset.le_max' s _ hb'
  omega

lemma leading_monomial (i : Fin N) (a : ℕ) :
    Leading (Pi.single i (Polynomial.X^a : K[X])) i a := by
  classical
  constructor
  · simp
  · intro j b h
    by_cases hj : j = i
    · subst j
      have : b ≠ a := by intro hb; subst b; omega
      simp [this]
    · simp [Pi.single_eq_of_ne hj]

lemma leading_smul {v : V K N} {i : Fin N} {a : ℕ} (h : Leading v i a)
    {c : K} (hc : c ≠ 0) : Leading (c • v) i a := by
  constructor
  · simpa using mul_ne_zero hc h.1
  · intro j b hj
    simp [h.2 j b hj]

lemma leading_X_pow {v : V K N} {i : Fin N} {a : ℕ} (h : Leading v i a)
    (m : ℕ) : Leading ((Polynomial.X^m : K[X]) • v) i (a+m) := by
  constructor
  · simpa only [Pi.smul_apply,smul_eq_mul,Polynomial.coeff_X_pow_mul,not_lt.mpr (by omega : m ≤ a+m),
      ite_false,Nat.add_sub_cancel] using h.1
  · intro j b hb
    simp only [Pi.smul_apply,smul_eq_mul,Polynomial.coeff_X_pow_mul']
    split_ifs with hbm
    · apply h.2
      have he : N*b = N*(b-m)+N*m := by rw [← Nat.mul_add,Nat.sub_add_cancel hbm]
      simp only [Nat.mul_add] at hb
      omega
    · rfl

lemma leading_add_of_lt {v w : V K N} {i j : Fin N} {a b : ℕ}
    (hv : Leading v i a) (hw : Leading w j b) (hlt : N*a+i.val < N*b+j.val) :
    Leading (v+w) j b := by
  constructor
  · simpa [hv.2 j b hlt] using hw.1
  · intro t c ht
    simp [hv.2 t c (by omega),hw.2 t c ht]

lemma leading_cancel {v w : V K N} {i : Fin N} {a : ℕ}
    (hv : Leading v i a) (hw : Leading w i a) :
    v - ((v i).coeff a / (w i).coeff a) • w = 0 ∨
    ∃ j b, Leading (v - ((v i).coeff a / (w i).coeff a) • w) j b ∧
      N*b+j.val < N*a+i.val := by
  classical
  let z := v - ((v i).coeff a / (w i).coeff a) • w
  by_cases hz : z = 0
  · exact Or.inl hz
  · right
    obtain ⟨j,b,hb⟩ := exists_leading hz
    refine ⟨j,b,hb,?_⟩
    by_contra hle
    have hzai : (z i).coeff a = 0 := by
      dsimp [z]
      simp [hw.1]
    rcases lt_or_eq_of_le (by omega : N*a+i.val ≤ N*b+j.val) with hlt | he
    · apply hb.1
      dsimp [z]
      simp [hv.2 j b hlt,hw.2 j b hlt]
    · obtain ⟨rfl,rfl⟩ := weight_injective he
      exact hb.1 hzai

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
attribute [local instance] Classical.propDecidable
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

def HasPivots (A : Submodule K[X] (V K N)) : Prop :=
  ∀ i : Fin N, ∃ a v, v ∈ A ∧ Leading v i a

lemma hasPivots_of_bound (A : Submodule K[X] (V K N)) (m : ℕ)
    (hm : ∀ i : Fin N, Pi.single i (Polynomial.X^m : K[X]) ∈ A) : HasPivots A := by
  intro i
  exact ⟨m,_,hm i,leading_monomial i m⟩

noncomputable def pivotDegree (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) : ℕ :=
  Nat.find (hA i)

lemma pivotDegree_min (A : Submodule K[X] (V K N)) (hA : HasPivots A)
    (i : Fin N) {v : V K N} (hv : v ∈ A) {a : ℕ} (ha : Leading v i a) :
    pivotDegree A hA i ≤ a := Nat.find_min' (hA i) ⟨v,hv,ha⟩

noncomputable def pivotRaw (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) : V K N :=
  Classical.choose (Nat.find_spec (hA i))

lemma pivotRaw_mem (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) :
    pivotRaw A hA i ∈ A := (Classical.choose_spec (Nat.find_spec (hA i))).1
lemma pivotRaw_leading (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) :
    Leading (pivotRaw A hA i) i (pivotDegree A hA i) :=
  (Classical.choose_spec (Nat.find_spec (hA i))).2

noncomputable def pivot (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) : V K N :=
  (((pivotRaw A hA i) i).coeff (pivotDegree A hA i))⁻¹ • pivotRaw A hA i

lemma pivot_mem (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) : pivot A hA i ∈ A :=
  (A.restrictScalars K).smul_mem _ (pivotRaw_mem A hA i)

lemma pivot_leading (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) :
    Leading (pivot A hA i) i (pivotDegree A hA i) :=
  leading_smul (pivotRaw_leading A hA i) (inv_ne_zero (pivotRaw_leading A hA i).1)

lemma pivot_monic (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) :
    ((pivot A hA i) i).coeff (pivotDegree A hA i) = 1 := by
  simp [pivot, (pivotRaw_leading A hA i).1]

lemma span_pivots (A : Submodule K[X] (V K N)) (hA : HasPivots A) :
    Submodule.span K[X] (Set.range (pivot A hA)) = A := by
  classical
  let B := Submodule.span K[X] (Set.range (pivot A hA))
  have hBA : B ≤ A := Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact pivot_mem A hA i)
  refine le_antisymm hBA ?_
  have step : ∀ k, ∀ (v : V K N) (i : Fin N) (a : ℕ), v ∈ A →
      Leading v i a → N*a+i.val = k → v ∈ B := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v i a hv hlead he
      have hai := pivotDegree_min A hA i hv hlead
      let w := (Polynomial.X^(a-pivotDegree A hA i) : K[X]) • pivot A hA i
      have hw : Leading w i a := by
        have hh := leading_X_pow (pivot_leading A hA i) (a-pivotDegree A hA i)
        simpa only [Nat.add_sub_of_le hai] using hh
      have hwB : w ∈ B := B.smul_mem _ (Submodule.subset_span ⟨i,rfl⟩)
      let c := (v i).coeff a / (w i).coeff a
      have hcB : c • w ∈ B := (B.restrictScalars K).smul_mem c hwB
      have hcA : c • w ∈ A := hBA hcB
      have hzA : v-c • w ∈ A := A.sub_mem hv hcA
      rcases leading_cancel hlead hw with hz | ⟨j,b,hz,hlt⟩
      · have hh : v = c • w := sub_eq_zero.mp hz
        exact hh ▸ hcB
      · have hzB := ih (N*b+j.val) (by omega) (v-c • w) j b hzA hz rfl
        have hh : v = (v-c • w)+c • w := (sub_add_cancel _ _).symm
        exact hh ▸ B.add_mem hzB hcB
  intro v hv
  by_cases hz : v = 0
  · exact hz ▸ B.zero_mem
  · obtain ⟨i,a,hlead⟩ := exists_leading hz
    exact step (N*a+i.val) v i a hv hlead rfl

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma leading_natDegree_le {v : V K N} {i : Fin N} {a : ℕ}
    (h : Leading v i a) (j : Fin N) : (v j).natDegree ≤ a := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro b hb
  apply h.2
  have hh := Nat.mul_le_mul_left N (show a+1 ≤ b by omega)
  simp only [Nat.mul_add,Nat.mul_one] at hh
  have hi := i.isLt
  omega

lemma leading_mul {v : V K N} {i : Fin N} {a : ℕ}
    (h : Leading v i a) (f : K[X]) (hf : f ≠ 0) :
    Leading (f • v) i (a+f.natDegree) := by
  constructor
  · change (f * v i).coeff (a+f.natDegree) ≠ 0
    rw [Nat.add_comm a,Polynomial.coeff_mul_add_eq_of_natDegree_le le_rfl (leading_natDegree_le h i)]
    exact mul_ne_zero (by simpa using Polynomial.leadingCoeff_ne_zero.mpr hf) h.1
  · intro j b hb
    change (f * v j).coeff b = 0
    rw [Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨c,d⟩ hcd
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hcd
    by_cases hc : f.natDegree < c
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hc,zero_mul]
    · have hcm := Nat.mul_le_mul_left N (show c ≤ f.natDegree by omega)
      have hbm : N*b = N*c+N*d := by rw [← Nat.mul_add,he]
      have hh : N*a+i.val < N*d+j.val := by
        simp only [Nat.mul_add] at hb
        omega
      rw [h.2 j d hh,mul_zero]

lemma independent_of_leading (b : Fin N → V K N) (a : Fin N → ℕ)
    (hb : ∀ i, Leading (b i) i (a i)) : LinearIndependent K[X] b := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro f hf
  by_contra hn
  push Not at hn
  obtain ⟨i,hi⟩ := hn
  let s := Finset.univ.filter (fun j => f j ≠ 0)
  have hs : s.Nonempty := ⟨i,by simp [s,hi]⟩
  let w := fun j : Fin N => N*(a j+(f j).natDegree)+j.val
  obtain ⟨j,hjs,hmax⟩ := Finset.exists_max_image s w hs
  have hj : f j ≠ 0 := (Finset.mem_filter.mp hjs).2
  have hlead := leading_mul (hb j) (f j) hj
  have hcoeff : ((∑ t : Fin N, f t • b t) j).coeff (a j+(f j).natDegree) =
      ((f j • b j) j).coeff (a j+(f j).natDegree) := by
    simp only [Finset.sum_apply,Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_single j
    · intro t _ ht
      by_cases ht0 : f t = 0
      · simp [ht0]
      · apply (leading_mul (hb t) (f t) ht0).2
        have hle := hmax t (show t ∈ s by simp [s,ht0])
        have hne : w t ≠ w j := by
          intro he
          exact ht (weight_injective he).1
        dsimp only [w] at hle hne
        omega
    · simp
  have hz : ((∑ t : Fin N, f t • b t) j).coeff (a j+(f j).natDegree) = 0 := by
    rw [hf]
    simp
  exact hlead.1 (hcoeff.symm.trans hz)

lemma independent_pivots (A : Submodule K[X] (V K N)) (hA : HasPivots A) :
    LinearIndependent K[X] (pivot A hA) :=
  independent_of_leading (pivot A hA) (pivotDegree A hA) (pivot_leading A hA)

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma reflect_sum {I : Type} (s : Finset I) (f : I → K[X]) (a : ℕ) :
    Polynomial.reflect a (∑ i ∈ s, f i) = ∑ i ∈ s, Polynomial.reflect a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,Polynomial.reflect_add,ih]

lemma polynomial_eq_one_of_dvd_X_pow (f : K[X]) (m : ℕ)
    (hf : f ∣ Polynomial.X^m) (hc : f.coeff 0 = 1) : f = 1 := by
  obtain ⟨a,_,ha⟩ := (dvd_prime_pow Polynomial.prime_X m).mp hf
  have ha0 : a = 0 := by
    by_contra hn
    have hX : Polynomial.X ∣ f := ha.dvd_iff_dvd_right.mpr
      (dvd_pow_self _ hn)
    have hz := Polynomial.X_dvd_iff.mp hX
    rw [hc] at hz
    exact one_ne_zero hz
  rw [ha0,pow_zero] at ha
  have hu : IsUnit f := ha.isUnit_iff.mpr isUnit_one
  obtain ⟨c,_,he⟩ := Polynomial.isUnit_iff.mp hu
  have hc1 : c = 1 := by simpa [← he] using hc
  rw [← he,hc1,Polynomial.C_1]

noncomputable def columnReflect (B : Matrix (Fin N) (Fin N) K[X]) (a : Fin N → ℕ) :
    Matrix (Fin N) (Fin N) K[X] := fun i j => Polynomial.reflect (a j) (B i j)

lemma columnReflect_det_eq_one (B C : Matrix (Fin N) (Fin N) K[X])
    (a : Fin N → ℕ) (m : ℕ) (hBC : B*C = (Polynomial.X^m : K[X]) • 1)
    (hB : ∀ i j, (B i j).natDegree ≤ a j)
    (hc : ((columnReflect B a).det).coeff 0 = 1) :
    (columnReflect B a).det = 1 := by
  classical
  let L := m + Finset.univ.sup (fun p : Fin N × Fin N => a p.1+(C p.1 p.2).natDegree)
  have hL : ∀ i j, a i+(C i j).natDegree ≤ L := by
    intro i j
    exact le_trans (Finset.le_sup (f := fun p : Fin N × Fin N => a p.1+(C p.1 p.2).natDegree)
      (Finset.mem_univ (i,j))) (Nat.le_add_left _ _)
  have hmL : m ≤ L := Nat.le_add_right _ _
  let D : Matrix (Fin N) (Fin N) K[X] := fun i j => Polynomial.reflect (L-a i) (C i j)
  have hGD : columnReflect B a * D = (Polynomial.X^(L-m) : K[X]) • 1 := by
    apply Matrix.ext
    intro i j
    change (∑ t, Polynomial.reflect (a t) (B i t) * Polynomial.reflect (L-a t) (C t j)) = _
    have he : (∑ t, Polynomial.reflect (a t) (B i t) * Polynomial.reflect (L-a t) (C t j)) =
        Polynomial.reflect L ((B*C) i j) := by
      rw [Matrix.mul_apply,reflect_sum]
      apply Finset.sum_congr rfl
      intro t _
      have hCt := hL t j
      have hh := Polynomial.reflect_mul (B i t) (C t j) (hB i t)
        (show (C t j).natDegree ≤ L-a t by omega)
      rw [Nat.add_sub_of_le (show a t ≤ L by omega)] at hh
      exact hh.symm
    rw [he,hBC]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one]
      rw [Polynomial.reflect_monomial,Polynomial.revAt_le hmL]
    · simp [hij]
  have hdet := congrArg Matrix.det hGD
  rw [Matrix.det_mul,Matrix.det_smul,Matrix.det_one,mul_one,Fintype.card_fin,← pow_mul] at hdet
  exact polynomial_eq_one_of_dvd_X_pow _ ((L-m)*N) ⟨D.det,hdet.symm⟩ hc

noncomputable def pivotMatrix (A : Submodule K[X] (V K N)) (hA : HasPivots A) :
    Matrix (Fin N) (Fin N) K[X] := fun i j => pivot A hA j i

lemma pivotMatrix_right_multiple (A : Submodule K[X] (V K N)) (hA : HasPivots A)
    (m : ℕ) (hm : ∀ i : Fin N, Pi.single i (Polynomial.X^m : K[X]) ∈ A) :
    ∃ C : Matrix (Fin N) (Fin N) K[X], pivotMatrix A hA*C = (Polynomial.X^m : K[X]) • 1 := by
  classical
  have hex : ∀ j : Fin N, ∃ c : Fin N → K[X],
      ∑ i, c i • pivot A hA i = Pi.single j (Polynomial.X^m : K[X]) := by
    intro j
    apply (Submodule.mem_span_range_iff_exists_fun K[X]).mp
    rw [span_pivots]
    exact hm j
  choose c hc using hex
  refine ⟨fun i j => c j i,?_⟩
  apply Matrix.ext
  intro i j
  have he := congr_fun (hc j) i
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at he
  change (∑ t, pivot A hA t i * c j t) = _
  simp only [mul_comm]
  rw [he]
  by_cases hij : i = j
  · subst j; simp
  · simp [hij]

lemma pivotMatrix_reflect_constant_upper (A : Submodule K[X] (V K N)) (hA : HasPivots A) :
    ((Polynomial.constantCoeff).mapMatrix (columnReflect (pivotMatrix A hA) (pivotDegree A hA))).IsUpperTriangular := by
  intro i j hij
  change Polynomial.constantCoeff (Polynomial.reflect (pivotDegree A hA j) (pivot A hA j i)) = 0
  rw [Polynomial.constantCoeff_apply,Polynomial.coeff_reflect,Polynomial.revAt_zero]
  apply (pivot_leading A hA j).2
  exact Nat.add_lt_add_left hij _

lemma pivotMatrix_reflect_det_constant (A : Submodule K[X] (V K N)) (hA : HasPivots A) :
    ((columnReflect (pivotMatrix A hA) (pivotDegree A hA)).det).coeff 0 = 1 := by
  classical
  rw [← Polynomial.constantCoeff_apply, RingHom.map_det,Matrix.det_of_isUpperTriangular (pivotMatrix_reflect_constant_upper A hA)]
  apply Finset.prod_eq_one
  intro i _
  change Polynomial.constantCoeff (Polynomial.reflect (pivotDegree A hA i) (pivot A hA i i)) = 1
  rw [Polynomial.constantCoeff_apply,Polynomial.coeff_reflect,Polynomial.revAt_zero]
  exact pivot_monic A hA i

theorem pivotMatrix_reflect_det (A : Submodule K[X] (V K N)) (hA : HasPivots A)
    (m : ℕ) (hm : ∀ i : Fin N, Pi.single i (Polynomial.X^m : K[X]) ∈ A) :
    (columnReflect (pivotMatrix A hA) (pivotDegree A hA)).det = 1 := by
  obtain ⟨C,hC⟩ := pivotMatrix_right_multiple A hA m hm
  exact columnReflect_det_eq_one _ C _ m hC (fun i j => leading_natDegree_le (pivot_leading A hA j) i)
    (pivotMatrix_reflect_det_constant A hA)

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices
variable (K : Type) [Field K] (N : ℕ)

noncomputable def polynomialEmbedding : (Fin N → K[X]) →ₗ[K[X]] V K N :=
  (standard K N).subtype.comp (polynomialToStandard K N)

@[simp] lemma polynomialEmbedding_apply (v : Fin N → K[X]) (i : Fin N) :
    polynomialEmbedding K N v i = algebraMap K[X] (RatFunc K) (v i) := rfl

noncomputable def polynomialLattice (A : Vertex K N) : Submodule K[X] (Fin N → K[X]) :=
  A.val.comap (polynomialEmbedding K N)

lemma polynomialLattice_map (A : Vertex K N) :
    (polynomialLattice K N A).map (polynomialEmbedding K N) = A.val := by
  apply le_antisymm
  · rintro v ⟨w,hw,rfl⟩
    exact hw
  · intro v hv
    obtain ⟨w,hw⟩ := (polynomialToStandard_bijective K N).2
      ⟨v,vertex_le (shift K N) (standard K N) A hv⟩
    refine ⟨w,?_,?_⟩
    · change polynomialEmbedding K N w ∈ A.val
      have he := congrArg Subtype.val hw
      change polynomialEmbedding K N w = v at he
      exact he.symm ▸ hv
    · exact congrArg Subtype.val hw

lemma polynomialLattice_bound (A : Vertex K N) :
    ∃ m : ℕ, ∀ i : Fin N, Pi.single i (Polynomial.X^m : K[X]) ∈ polynomialLattice K N A := by
  classical
  obtain ⟨m,hm⟩ := vertex_bounded (shift K N) (standard K N) A
  refine ⟨m,fun i => ?_⟩
  change polynomialEmbedding K N (Pi.single i (Polynomial.X^m : K[X])) ∈ A.val
  apply hm
  apply (mem_level K N _ _ _).mpr
  refine ⟨Pi.single i (1 : RatFunc K),(by intro j; exact ⟨(if j = i then 1 else 0 : K[X]),by split_ifs <;> simp_all⟩),?_⟩
  funext j
  by_cases hij : j = i
  · subst j; simp [Algebra.smul_def]
  · simp [hij,Algebra.smul_def]

lemma polynomialHasPivots (A : Vertex K N) :
    PolynomialVectors.HasPivots (polynomialLattice K N A) := by
  obtain ⟨m,hm⟩ := polynomialLattice_bound K N A
  exact PolynomialVectors.hasPivots_of_bound _ m hm

noncomputable def diagonalExponents (A : Vertex K N) : Fin N → ℕ :=
  PolynomialVectors.pivotDegree (polynomialLattice K N A) (polynomialHasPivots K N A)

noncomputable def birkhoffSL (A : Vertex K N) : Matrix.SpecialLinearGroup (Fin N) K[X] :=
  ⟨PolynomialVectors.columnReflect
    (PolynomialVectors.pivotMatrix (polynomialLattice K N A) (polynomialHasPivots K N A))
    (diagonalExponents K N A),by
      obtain ⟨m,hm⟩ := polynomialLattice_bound K N A
      exact PolynomialVectors.pivotMatrix_reflect_det _ _ m hm⟩

lemma birkhoffSL_constant (A : Vertex K N) (i j : Fin N) (hji : j ≤ i) :
    (birkhoffSL K N A i j).coeff 0 = (1 : Matrix (Fin N) (Fin N) K) i j := by
  classical
  change (Polynomial.reflect (diagonalExponents K N A j)
    (PolynomialVectors.pivot (polynomialLattice K N A) (polynomialHasPivots K N A) j i)).coeff 0 = _
  rw [Polynomial.coeff_reflect,Polynomial.revAt_zero]
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply_eq]
    exact PolynomialVectors.pivot_monic _ _ i
  · rw [Matrix.one_apply_ne hij]
    apply (PolynomialVectors.pivot_leading (polynomialLattice K N A) (polynomialHasPivots K N A) j).2
    have hj : j < i := lt_of_le_of_ne hji (Ne.symm hij)
    exact Nat.add_lt_add_left hj _

lemma positive_reflect_uniformizer (f : K[X]) (a : ℕ) (hf : f.natDegree ≤ a) :
    positive K (Polynomial.reflect a f) * uniformizer K^a = algebraMap K[X] (RatFunc K) f := by
  let : Invertible (uniformizer K) := invertibleOfNonzero (uniformizer_ne_zero K)
  change Polynomial.eval₂ (algebraMap K (RatFunc K)) (uniformizer K)⁻¹ (Polynomial.reflect a f) * uniformizer K^a = _
  simpa only [invOf_eq_inv,eval_uniformizer] using
    Polynomial.eval₂_reflect_mul_pow (algebraMap K (RatFunc K)) (uniformizer K) a f hf

noncomputable def exponentLattice (a : Fin N → ℕ) : LatticeSpace K N :=
  Submodule.span K[X] (Set.range fun i : Fin N => Pi.single i (uniformizer K ^ a i))

lemma birkhoffSL_column (A : Vertex K N) (j : Fin N) :
    positiveLinear K N (birkhoffSL K N A)
      (Pi.single j (uniformizer K ^ diagonalExponents K N A j)) =
    polynomialEmbedding K N (PolynomialVectors.pivot (polynomialLattice K N A) (polynomialHasPivots K N A) j) := by
  classical
  rw [positiveLinear_apply,Matrix.mulVec_single]
  funext i
  change positive K (Polynomial.reflect (diagonalExponents K N A j)
    (PolynomialVectors.pivot (polynomialLattice K N A) (polynomialHasPivots K N A) j i)) *
    uniformizer K ^ diagonalExponents K N A j = _
  exact positive_reflect_uniformizer K _ _
    (PolynomialVectors.leading_natDegree_le (PolynomialVectors.pivot_leading _ _ j) i)

theorem birkhoff_lattice (A : Vertex K N) :
    positiveAction K N (birkhoffSL K N A) (exponentLattice K N (diagonalExponents K N A)) = A.val := by
  change (Submodule.span K[X] (Set.range fun i : Fin N => Pi.single i (uniformizer K ^ diagonalExponents K N A i))).map
    (positiveLinear K N (birkhoffSL K N A)).toLinearMap = A.val
  rw [Submodule.map_span,← Set.range_comp]
  have he : (fun i : Fin N => positiveLinear K N (birkhoffSL K N A)
      (Pi.single i (uniformizer K ^ diagonalExponents K N A i))) =
      fun i => polynomialEmbedding K N (PolynomialVectors.pivot (polynomialLattice K N A) (polynomialHasPivots K N A) i) :=
    funext (birkhoffSL_column K N A)
  change Submodule.span K[X] (Set.range (fun i : Fin N => positiveLinear K N (birkhoffSL K N A)
    (Pi.single i (uniformizer K ^ diagonalExponents K N A i)))) = A.val
  rw [he]
  change Submodule.span K[X] (Set.range ((polynomialEmbedding K N) ∘
    PolynomialVectors.pivot (polynomialLattice K N A) (polynomialHasPivots K N A))) = A.val
  rw [Set.range_comp,← Submodule.map_span,PolynomialVectors.span_pivots,polynomialLattice_map]

end CoboundaryExpanders.RationalLattices

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma span_of_minimal (A : Submodule K[X] (V K N))
    (b : Fin N → V K N) (degree : Fin N → ℕ)
    (hb : ∀ i, b i ∈ A) (hbLead : ∀ i, Leading (b i) i (degree i))
    (hmin : ∀ {v : V K N} {i : Fin N} {r : ℕ}, v ∈ A → Leading v i r → degree i ≤ r) :
    Submodule.span K[X] (Set.range (b)) = A := by
  classical
  let B := Submodule.span K[X] (Set.range (b))
  have hBA : B ≤ A := Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hb i)
  refine le_antisymm hBA ?_
  have step : ∀ k, ∀ (v : V K N) (i : Fin N) (a : ℕ), v ∈ A →
      Leading v i a → N*a+i.val = k → v ∈ B := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v i a hv hlead he
      have hai := hmin hv hlead
      let w := (Polynomial.X^(a-degree i) : K[X]) • b i
      have hw : Leading w i a := by
        have hh := leading_X_pow (hbLead i) (a-degree i)
        simpa only [Nat.add_sub_of_le hai] using hh
      have hwB : w ∈ B := B.smul_mem _ (Submodule.subset_span ⟨i,rfl⟩)
      let c := (v i).coeff a / (w i).coeff a
      have hcB : c • w ∈ B := (B.restrictScalars K).smul_mem c hwB
      have hcA : c • w ∈ A := hBA hcB
      have hzA : v-c • w ∈ A := A.sub_mem hv hcA
      rcases leading_cancel hlead hw with hz | ⟨j,b,hz,hlt⟩
      · have hh : v = c • w := sub_eq_zero.mp hz
        exact hh ▸ hcB
      · have hzB := ih (N*b+j.val) (by omega) (v-c • w) j b hzA hz rfl
        have hh : v = (v-c • w)+c • w := (sub_add_cancel _ _).symm
        exact hh ▸ B.add_mem hzB hcB
  intro v hv
  by_cases hz : v = 0
  · exact hz ▸ B.zero_mem
  · obtain ⟨i,a,hlead⟩ := exists_leading hz
    exact step (N*a+i.val) v i a hv hlead rfl

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma pivotDegree_antitone {A B : Submodule K[X] (V K N)} (hA : HasPivots A) (hB : HasPivots B)
    (hBA : B ≤ A) (i : Fin N) : pivotDegree A hA i ≤ pivotDegree B hB i :=
  pivotDegree_min A hA i (hBA (pivot_mem B hB i)) (pivot_leading B hB i)

lemma eq_of_le_same_pivots {A B : Submodule K[X] (V K N)} (hA : HasPivots A) (hB : HasPivots B)
    (hBA : B ≤ A) (hdeg : ∀ i, pivotDegree A hA i = pivotDegree B hB i) : A = B := by
  have hAspan := span_of_minimal A (pivot B hB) (pivotDegree B hB)
    (fun i => hBA (pivot_mem B hB i)) (pivot_leading B hB)
    (fun hv hl => by rw [← hdeg]; exact pivotDegree_min A hA _ hv hl)
  exact hAspan.symm.trans (span_pivots B hB)

noncomputable def powerLinear (m : ℕ) : V K N →ₗ[K[X]] V K N where
  toFun v := (Polynomial.X^m : K[X]) • v
  map_add' v w := smul_add _ _ _
  map_smul' c v := by simp [smul_smul,mul_comm]

noncomputable def powerShift (A : Submodule K[X] (V K N)) (m : ℕ) : Submodule K[X] (V K N) :=
  A.map (powerLinear m)

lemma powerShift_le (A : Submodule K[X] (V K N)) (m : ℕ) : powerShift A m ≤ A := by
  rintro v ⟨w,hw,rfl⟩
  exact A.smul_mem _ hw

lemma powerShift_hasPivots (A : Submodule K[X] (V K N)) (hA : HasPivots A) (m : ℕ) :
    HasPivots (powerShift A m) := by
  intro i
  refine ⟨pivotDegree A hA i+m,(Polynomial.X^m : K[X]) • pivot A hA i,?_,?_⟩
  · exact ⟨pivot A hA i,pivot_mem A hA i,rfl⟩
  · exact leading_X_pow (pivot_leading A hA i) m

lemma pivotDegree_powerShift (A : Submodule K[X] (V K N)) (hA : HasPivots A) (m : ℕ) (i : Fin N) :
    pivotDegree (powerShift A m) (powerShift_hasPivots A hA m) i = pivotDegree A hA i+m := by
  let hS := powerShift_hasPivots A hA m
  apply le_antisymm
  · exact pivotDegree_min _ hS i ⟨pivot A hA i,pivot_mem A hA i,rfl⟩
      (leading_X_pow (pivot_leading A hA i) m)
  · obtain ⟨v,hv,he⟩ := pivot_mem (powerShift A m) hS i
    have hv0 : v ≠ 0 := by
      intro hz
      have hh := leading_ne_zero (pivot_leading (powerShift A m) hS i)
      apply hh
      rw [← he,hz,map_zero]
    obtain ⟨j,b,hb⟩ := exists_leading hv0
    have hl : Leading ((Polynomial.X^m : K[X]) • v) i (pivotDegree (powerShift A m) hS i) := by
      change Leading (powerLinear m v) i _
      rw [he]
      exact pivot_leading _ hS i
    obtain ⟨hji,hd⟩ := leading_unique (leading_X_pow hb m) hl
    subst j
    have hmin := pivotDegree_min A hA i hv hb
    change pivotDegree A hA i + m ≤ pivotDegree (powerShift A m) hS i
    omega

lemma interval_pivot_increment {A B : Submodule K[X] (V K N)} (hA : HasPivots A) (hB : HasPivots B)
    (hBA : B ≤ A) (hAB : powerShift A 1 ≤ B) (i : Fin N) :
    pivotDegree B hB i = pivotDegree A hA i ∨ pivotDegree B hB i = pivotDegree A hA i+1 := by
  have hlo := pivotDegree_antitone hA hB hBA i
  have hhi := pivotDegree_antitone hB (powerShift_hasPivots A hA 1) hAB i
  rw [pivotDegree_powerShift A hA 1 i] at hhi
  omega

noncomputable def incrementSet (A B : Submodule K[X] (V K N)) (hA : HasPivots A) (hB : HasPivots B) : Finset (Fin N) :=
  Finset.univ.filter (fun i => pivotDegree A hA i < pivotDegree B hB i)

lemma incrementSet_mono {A B C : Submodule K[X] (V K N)}
    (hA : HasPivots A) (hB : HasPivots B) (hC : HasPivots C) (hCB : C ≤ B) :
    incrementSet A B hA hB ⊆ incrementSet A C hA hC := by
  classical
  intro i hi
  simp only [incrementSet,Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
  exact lt_of_lt_of_le hi (pivotDegree_antitone hB hC hCB i)

lemma interval_incrementSet_eq_iff {A B C : Submodule K[X] (V K N)}
    (hA : HasPivots A) (hB : HasPivots B) (hC : HasPivots C)
    (hBA : B ≤ A) (hCB : C ≤ B) (hAC : powerShift A 1 ≤ C) :
    incrementSet A B hA hB = incrementSet A C hA hC ↔ B = C := by
  classical
  constructor
  · intro he
    apply eq_of_le_same_pivots hB hC hCB
    intro i
    have hb := interval_pivot_increment hA hB hBA (hAC.trans hCB) i
    have hc := interval_pivot_increment hA hC (hCB.trans hBA) hAC i
    have hh := Finset.ext_iff.mp he i
    simp only [incrementSet,Finset.mem_filter,Finset.mem_univ,true_and] at hh
    omega
  · rintro rfl
    rfl

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N M : ℕ}

theorem simultaneous_minimal_basis
    (A : Submodule K[X] (V K N)) (hA : HasPivots A)
    (B : Fin (M+1) → Submodule K[X] (V K N))
    (hB : ∀ r, HasPivots (B r)) (hanti : Antitone B)
    (hzero : B 0 = A) (hbelow : ∀ r, powerShift A 1 ≤ B r) :
    ∃ b : Fin N → V K N,
      (∀ i, b i ∈ A) ∧ (∀ i, Leading (b i) i (pivotDegree A hA i)) ∧
      (∀ i, (b i i).coeff (pivotDegree A hA i) = 1) ∧
      ∀ r, Submodule.span K[X] (Set.range fun i =>
        if pivotDegree (B r) (hB r) i = pivotDegree A hA i
        then b i else (Polynomial.X : K[X]) • b i) = B r := by
  classical
  let S (i : Fin N) : Finset (Fin (M+1)) :=
    Finset.univ.filter (fun r => pivotDegree (B r) (hB r) i = pivotDegree A hA i)
  have hS (i : Fin N) : (S i).Nonempty := by
    refine ⟨0,?_⟩
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    subst A
    rfl
  let last (i : Fin N) := (S i).max' (hS i)
  have hlast (i : Fin N) : pivotDegree (B (last i)) (hB (last i)) i = pivotDegree A hA i := by
    have hh := Finset.max'_mem (S i) (hS i)
    exact (Finset.mem_filter.mp hh).2
  let b (i : Fin N) := pivot (B (last i)) (hB (last i)) i
  have hmem (i : Fin N) : b i ∈ A := by
    rw [← hzero]
    exact hanti (Fin.zero_le _) (pivot_mem _ _ _)
  have hlead (i : Fin N) : Leading (b i) i (pivotDegree A hA i) := by
    rw [← hlast i]
    exact pivot_leading _ _ _
  refine ⟨b,hmem,hlead,?_,?_⟩
  · intro i
    rw [← hlast i]
    exact pivot_monic _ _ _
  · intro r
    let c (i : Fin N) := if pivotDegree (B r) (hB r) i = pivotDegree A hA i
      then b i else (Polynomial.X : K[X]) • b i
    have hBA : B r ≤ A := by rw [← hzero]; exact hanti (Fin.zero_le _)
    have hinc (i : Fin N) := interval_pivot_increment hA (hB r) hBA (hbelow r) i
    have hc (i : Fin N) : c i ∈ B r := by
      dsimp [c]
      split_ifs with he
      · have hr : r ∈ S i := Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩
        have hrlast : r ≤ last i := Finset.le_max' (S i) r hr
        exact hanti hrlast (pivot_mem _ _ _)
      · apply hbelow r
        refine ⟨b i,hmem i,?_⟩
        simp [powerLinear]
    have hcl (i : Fin N) : Leading (c i) i (pivotDegree (B r) (hB r) i) := by
      dsimp [c]
      split_ifs with he
      · rw [he]; exact hlead i
      · have hh : pivotDegree (B r) (hB r) i = pivotDegree A hA i+1 := (hinc i).resolve_left he
        rw [hh]
        simpa using leading_X_pow (hlead i) 1
    exact span_of_minimal (B r) c (pivotDegree (B r) (hB r)) hc hcl
      (fun hv hl => pivotDegree_min _ _ _ hv hl)

lemma matrix_right_multiple_of_span (b : Fin N → V K N)
    (A : Submodule K[X] (V K N)) (hspan : Submodule.span K[X] (Set.range b) = A)
    (m : ℕ) (hm : ∀ i : Fin N, Pi.single i (Polynomial.X^m : K[X]) ∈ A) :
    ∃ C : Matrix (Fin N) (Fin N) K[X], (show Matrix (Fin N) (Fin N) K[X] from fun i j => b j i)*C = (Polynomial.X^m : K[X]) • 1 := by
  classical
  have hex : ∀ j : Fin N, ∃ c : Fin N → K[X],
      ∑ i, c i • b i = Pi.single j (Polynomial.X^m : K[X]) := by
    intro j
    apply (Submodule.mem_span_range_iff_exists_fun K[X]).mp
    rw [hspan]
    exact hm j
  choose c hc using hex
  refine ⟨fun i j => c j i,?_⟩
  apply Matrix.ext
  intro i j
  have he := congr_fun (hc j) i
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at he
  change (∑ t, b t i * c j t) = (Polynomial.X^m : K[X]) * (if i = j then 1 else 0)
  have he' : (∑ t, c j t * b t i) = (Polynomial.X^m : K[X]) * (if i = j then 1 else 0) := by
    by_cases hij : i = j
    · subst j; simpa using he
    · simpa [hij] using he
  exact (Finset.sum_congr rfl (fun _ _ => mul_comm _ _)).trans he'

lemma monic_reflect_det (b : Fin N → V K N) (a : Fin N → ℕ)
    (hl : ∀ i, Leading (b i) i (a i)) (hmonic : ∀ i, (b i i).coeff (a i) = 1)
    (A : Submodule K[X] (V K N)) (hspan : Submodule.span K[X] (Set.range b) = A)
    (m : ℕ) (hm : ∀ i : Fin N, Pi.single i (Polynomial.X^m : K[X]) ∈ A) :
    (columnReflect (fun i j => b j i) a).det = 1 := by
  classical
  obtain ⟨C,hC⟩ := matrix_right_multiple_of_span b A hspan m hm
  apply columnReflect_det_eq_one _ C a m hC (fun i j => leading_natDegree_le (hl j) i)
  have hupper : ((Polynomial.constantCoeff).mapMatrix (columnReflect (fun i j => b j i) a)).IsUpperTriangular := by
    intro i j hij
    change Polynomial.constantCoeff (Polynomial.reflect (a j) (b j i)) = 0
    rw [Polynomial.constantCoeff_apply,Polynomial.coeff_reflect,Polynomial.revAt_zero]
    exact (hl j).2 _ _ (Nat.add_lt_add_left hij _)
  rw [← Polynomial.constantCoeff_apply,RingHom.map_det,Matrix.det_of_isUpperTriangular hupper]
  apply Finset.prod_eq_one
  intro i _
  change Polynomial.constantCoeff (Polynomial.reflect (a i) (b i i)) = 1
  rw [Polynomial.constantCoeff_apply,Polynomial.coeff_reflect,Polynomial.revAt_zero]
  exact hmonic i

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma full_chain_permutation (S : Fin (N+1) → Finset (Fin N)) (hS : StrictMono S) :
    ∃ σ : Equiv.Perm (Fin N), ∀ r : Fin N,
      S r.succ = insert (σ r) (S r.castSucc) ∧ σ r ∉ S r.castSucc := by
  classical
  have hcard (r : Fin (N+1)) : (S r).card = r.val := by
    let f (r : Fin (N+1)) : Fin (N+1) := ⟨(S r).card,
      Nat.lt_succ_of_le (by simpa using Finset.card_le_card (Finset.subset_univ (S r)))⟩
    have hf : StrictMono f := by
      intro r s hrs
      exact Finset.card_lt_card (hS hrs)
    have he := congr_fun hf.eq_id r
    exact congrArg Fin.val he
  have hex (r : Fin N) : ∃ i : Fin N, S r.succ = insert i (S r.castSucc) ∧ i ∉ S r.castSucc := by
    have hsub := hS.monotone (show r.castSucc ≤ r.succ from Nat.le_succ r.val)
    have hd : (S r.succ \ S r.castSucc).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub,hcard,hcard]
      simp
    obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hd
    refine ⟨i,?_,?_⟩
    · ext j
      have hh := Finset.ext_iff.mp hi j
      simp only [Finset.mem_sdiff,Finset.mem_singleton] at hh
      simp only [Finset.mem_insert]
      constructor
      · intro hj
        by_cases hj0 : j ∈ S r.castSucc
        · exact Or.inr hj0
        · exact Or.inl (hh.mp ⟨hj,hj0⟩)
      · rintro (rfl|hj)
        · exact (hh.mpr rfl).1
        · exact hsub hj
    · have hh : i ∈ S r.succ \ S r.castSucc := by rw [hi]; simp
      exact (Finset.mem_sdiff.mp hh).2
  choose σ hσ using hex
  have hinj : Function.Injective σ := by
    suffices hh : ∀ i j : Fin N, i < j → σ i ≠ σ j by
      intro i j he
      rcases lt_trichotomy i j with h | h | h
      · exact False.elim (hh i j h he)
      · exact h
      · exact False.elim (hh j i h he.symm)
    intro i j hij he
    have hle : i.succ ≤ j.castSucc := by
      change i.val+1 ≤ j.val
      exact hij
    have hmem : σ i ∈ S i.succ := by rw [(hσ i).1]; simp
    have hh := hS.monotone hle hmem
    rw [he] at hh
    exact (hσ j).2 hh
  let e : Equiv.Perm (Fin N) := Equiv.ofBijective σ
    ⟨hinj,Finite.surjective_of_injective hinj⟩
  exact ⟨e,hσ⟩

theorem full_flag_increment_permutation
    (A : Submodule K[X] (V K N)) (hA : HasPivots A)
    (B : Fin (N+1) → Submodule K[X] (V K N))
    (hB : ∀ r, HasPivots (B r)) (hanti : StrictAnti B)
    (hzero : B 0 = A) (hbelow : ∀ r, powerShift A 1 ≤ B r) :
    ∃ σ : Equiv.Perm (Fin N), ∀ r : Fin N,
      incrementSet A (B r.succ) hA (hB r.succ) =
        insert (σ r) (incrementSet A (B r.castSucc) hA (hB r.castSucc)) ∧
      σ r ∉ incrementSet A (B r.castSucc) hA (hB r.castSucc) := by
  apply full_chain_permutation (fun r => incrementSet A (B r) hA (hB r))
  intro r s hrs
  have hBA : B r ≤ A := by rw [← hzero]; exact hanti.antitone (Fin.zero_le _)
  have hSB := hanti hrs
  have hsub := incrementSet_mono hA (hB r) (hB s) hSB.le
  apply lt_of_le_of_ne hsub
  intro he
  have hsame := (interval_incrementSet_eq_iff hA (hB r) (hB s) hBA hSB.le (hbelow s)).mp he
  exact hSB.ne hsame.symm

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.PolynomialVectors
open scoped Polynomial BigOperators
variable {K : Type} [Field K] {N : ℕ}

lemma leading_weight_bound {v : V K N} {i : Fin N} {a : ℕ}
    (h : Leading v i a) (j : Fin N) (hj : v j ≠ 0) :
    N*(v j).natDegree+j.val ≤ N*a+i.val := by
  by_contra hn
  have hc := h.2 j (v j).natDegree (by omega)
  exact (Polynomial.leadingCoeff_ne_zero.mpr hj) hc

lemma leading_pivot_natDegree {v : V K N} {i : Fin N} {a : ℕ}
    (h : Leading v i a) : (v i).natDegree = a :=
  le_antisymm (leading_natDegree_le h i) (Polynomial.le_natDegree_of_ne_zero h.1)

lemma leading_mulVec (C : Matrix (Fin N) (Fin N) K[X]) (M : ℕ)
    (hC : ∀ j, Leading (fun i => C i j) j M)
    {v : V K N} {i : Fin N} {a : ℕ} (hv : Leading v i a) :
    Leading (C.mulVec v) i (a+M) := by
  classical
  have he : C.mulVec v = ∑ j, v j • (fun k => C k j) := by
    funext k
    simp only [Matrix.mulVec,dotProduct,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [he]
  have hv0 : v i ≠ 0 := by intro hz; simpa [hz] using hv.1
  have hi : Leading (v i • fun k => C k i) i (a+M) := by
    simpa [leading_pivot_natDegree hv,Nat.add_comm] using leading_mul (hC i) (v i) hv0
  constructor
  · have hh : ((∑ j, v j • (fun k => C k j)) i).coeff (a+M) =
        ((v i • fun k => C k i) i).coeff (a+M) := by
      simp only [Finset.sum_apply,Polynomial.finsetSum_coeff]
      apply Finset.sum_eq_single i
      · intro j _ hji
        by_cases hj0 : v j = 0
        · simp [hj0]
        · apply (leading_mul (hC j) (v j) hj0).2
          have hj := leading_weight_bound hv j hj0
          have hne : N*(v j).natDegree+j.val ≠ N*a+i.val := by
            intro heq
            exact hji (weight_injective heq).1
          simp only [Nat.mul_add]
          omega
      · simp
    rw [hh]
    exact hi.1
  · intro k e he
    simp only [Finset.sum_apply,Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj0 : v j = 0
    · simp [hj0]
    · apply (leading_mul (hC j) (v j) hj0).2
      have hj := leading_weight_bound hv j hj0
      simp only [Nat.mul_add] at he ⊢
      omega

lemma reflected_columns_leading (g : Matrix (Fin N) (Fin N) K[X]) (M : ℕ)
    (hdeg : ∀ i j, (g i j).natDegree ≤ M)
    (hc : ∀ i j, j ≤ i → (g i j).coeff 0 = (1 : Matrix (Fin N) (Fin N) K) i j) :
    ∀ j, Leading (fun i => Polynomial.reflect M (g i j)) j M := by
  classical
  intro j
  constructor
  · rw [Polynomial.coeff_reflect,Polynomial.revAt_le le_rfl,Nat.sub_self,hc j j le_rfl,Matrix.one_apply_eq]
    exact one_ne_zero
  · intro i b hb
    by_cases hMb : M < b
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        ((Polynomial.natDegree_reflect_le.trans (max_le le_rfl (hdeg i j))).trans_lt hMb)
    · have hbM : b = M := by
        by_contra hn
        have hm := Nat.mul_le_mul_left N (show b+1 ≤ M by omega)
        simp only [Nat.mul_add,Nat.mul_one] at hm
        have hi := i.isLt
        omega
      subst b
      have hji : j < i := by omega
      rw [Polynomial.coeff_reflect,Polynomial.revAt_le le_rfl,Nat.sub_self,hc i j hji.le,
        Matrix.one_apply_ne (ne_of_gt hji)]

noncomputable def matrixLinear (C : Matrix (Fin N) (Fin N) K[X]) : V K N →ₗ[K[X]] V K N :=
  Matrix.toLin' C

lemma image_hasPivots (C : Matrix (Fin N) (Fin N) K[X]) (M : ℕ)
    (hC : ∀ j, Leading (fun i => C i j) j M)
    (A : Submodule K[X] (V K N)) (hA : HasPivots A) :
    HasPivots (A.map (matrixLinear C)) := by
  intro i
  refine ⟨pivotDegree A hA i+M,C.mulVec (pivot A hA i),?_,?_⟩
  · exact ⟨pivot A hA i,pivot_mem A hA i,rfl⟩
  · exact leading_mulVec C M hC (pivot_leading _ _ _)

theorem pivotDegree_image (C : Matrix (Fin N) (Fin N) K[X]) (M : ℕ)
    (hC : ∀ j, Leading (fun i => C i j) j M)
    (A : Submodule K[X] (V K N)) (hA : HasPivots A) (i : Fin N) :
    pivotDegree (A.map (matrixLinear C)) (image_hasPivots C M hC A hA) i =
      pivotDegree A hA i+M := by
  let hI := image_hasPivots C M hC A hA
  apply le_antisymm
  · exact pivotDegree_min _ hI i ⟨pivot A hA i,pivot_mem A hA i,rfl⟩
      (leading_mulVec C M hC (pivot_leading _ _ _))
  · obtain ⟨v,hv,he⟩ := pivot_mem (A.map (matrixLinear C)) hI i
    have hv0 : v ≠ 0 := by
      intro hz
      apply leading_ne_zero (pivot_leading (A.map (matrixLinear C)) hI i)
      rw [← he,hz,map_zero]
    obtain ⟨j,a,hl⟩ := exists_leading hv0
    have ht := leading_mulVec C M hC hl
    change Leading (matrixLinear C v) j (a+M) at ht
    rw [he] at ht
    obtain ⟨hji,hd⟩ := leading_unique ht (pivot_leading _ hI i)
    subst j
    have hmin := pivotDegree_min A hA i hv hl
    change pivotDegree A hA i+M ≤ pivotDegree (A.map (matrixLinear C)) hI i
    omega

end CoboundaryExpanders.PolynomialVectors

namespace CoboundaryExpanders.RationalLattices
open scoped Polynomial BigOperators
open AffineLattices
variable (K : Type) [Field K] (N M : ℕ)

lemma polynomialLattice_mono {A B : Vertex K N} (hBA : B.val ≤ A.val) :
    polynomialLattice K N B ≤ polynomialLattice K N A :=
  Submodule.comap_mono hBA

lemma polynomialLattice_power_le {A B : Vertex K N}
    (hAB : level (shift K N) A.val 1 ≤ B.val) :
    PolynomialVectors.powerShift (polynomialLattice K N A) 1 ≤ polynomialLattice K N B := by
  rintro v ⟨w,hw,rfl⟩
  change polynomialEmbedding K N (PolynomialVectors.powerLinear 1 w) ∈ B.val
  apply hAB
  apply (mem_level K N _ _ _).mpr
  refine ⟨polynomialEmbedding K N w,hw,?_⟩
  funext i
  simp [PolynomialVectors.powerLinear,Algebra.smul_def]

theorem lattice_flag_birkhoff (B : Fin (M+1) → Vertex K N)
    (hanti : Antitone (fun r => (B r).val))
    (hbelow : ∀ r, level (shift K N) (B 0).val 1 ≤ (B r).val) :
    ∃ g : Matrix.SpecialLinearGroup (Fin N) K[X],
      (∀ i j : Fin N, j ≤ i → (g i j).coeff 0 = (1 : Matrix (Fin N) (Fin N) K) i j) ∧
      ∀ r, positiveAction K N g (exponentLattice K N (diagonalExponents K N (B r))) = (B r).val := by
  classical
  let A := polynomialLattice K N (B 0)
  let P (r : Fin (M+1)) := polynomialLattice K N (B r)
  let hA := polynomialHasPivots K N (B 0)
  let hP (r : Fin (M+1)) := polynomialHasPivots K N (B r)
  let a := PolynomialVectors.pivotDegree A hA
  obtain ⟨b,hb,hl,hmonic,hspan⟩ := PolynomialVectors.simultaneous_minimal_basis A hA P hP
    (fun r s hrs => polynomialLattice_mono K N (hanti hrs)) rfl
    (fun r => polynomialLattice_power_le K N (hbelow r))
  have hspan0 : Submodule.span K[X] (Set.range b) = A := by
    simpa only [P,A,↓reduceIte] using hspan 0
  obtain ⟨m,hm⟩ := polynomialLattice_bound K N (B 0)
  let g : Matrix.SpecialLinearGroup (Fin N) K[X] :=
    ⟨PolynomialVectors.columnReflect (fun i j => b j i) a,
      PolynomialVectors.monic_reflect_det b a hl hmonic A hspan0 m hm⟩
  refine ⟨g,?_,?_⟩
  · intro i j hji
    change (Polynomial.reflect (a j) (b j i)).coeff 0 = _
    rw [Polynomial.coeff_reflect,Polynomial.revAt_zero]
    by_cases hij : i = j
    · subst j; rw [Matrix.one_apply_eq]; exact hmonic i
    · rw [Matrix.one_apply_ne hij]
      have hj : j < i := lt_of_le_of_ne hji (Ne.symm hij)
      exact (hl j).2 i (a j) (Nat.add_lt_add_left hj _)
  · intro r
    let c (i : Fin N) := if PolynomialVectors.pivotDegree (P r) (hP r) i = a i
      then b i else (Polynomial.X : K[X]) • b i
    have hinc (i : Fin N) := PolynomialVectors.interval_pivot_increment hA (hP r)
      (polynomialLattice_mono K N (hanti (Fin.zero_le r)))
      (polynomialLattice_power_le K N (hbelow r)) i
    have hcol (j : Fin N) : positiveLinear K N g
        (Pi.single j (uniformizer K ^ diagonalExponents K N (B r) j)) = polynomialEmbedding K N (c j) := by
      rw [positiveLinear_apply,Matrix.mulVec_single]
      funext i
      change positive K (Polynomial.reflect (a j) (b j i)) *
        uniformizer K ^ PolynomialVectors.pivotDegree (P r) (hP r) j =
        algebraMap K[X] (RatFunc K) (c j i)
      have hh := positive_reflect_uniformizer K (b j i) (a j)
        (PolynomialVectors.leading_natDegree_le (hl j) i)
      dsimp only [c]
      split_ifs with he
      · rw [he]; exact hh
      · have he' : PolynomialVectors.pivotDegree (P r) (hP r) j = a j+1 := (hinc j).resolve_left he
        rw [he',pow_succ,← mul_assoc,hh]
        change algebraMap K[X] (RatFunc K) (b j i) * uniformizer K =
          algebraMap K[X] (RatFunc K) (Polynomial.X * b j i)
        rw [map_mul]
        exact mul_comm _ _
    change (Submodule.span K[X] (Set.range fun i : Fin N =>
      Pi.single i (uniformizer K ^ diagonalExponents K N (B r) i))).map
      (positiveLinear K N g).toLinearMap = (B r).val
    rw [Submodule.map_span,← Set.range_comp]
    change Submodule.span K[X] (Set.range (fun i : Fin N => positiveLinear K N g
      (Pi.single i (uniformizer K ^ diagonalExponents K N (B r) i)))) = (B r).val
    rw [show (fun i : Fin N => positiveLinear K N g (Pi.single i (uniformizer K ^ diagonalExponents K N (B r) i))) =
      fun i => polynomialEmbedding K N (c i) from funext hcol]
    change Submodule.span K[X] (Set.range ((polynomialEmbedding K N) ∘ c)) = (B r).val
    rw [Set.range_comp,← Submodule.map_span]
    have hs : Submodule.span K[X] (Set.range c) = P r := hspan r
    rw [hs]
    exact polynomialLattice_map K N (B r)

end CoboundaryExpanders.RationalLattices

end

end OAI
