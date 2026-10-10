import OAI.Geometry.HarmonicGrowth.PolynomialControl

namespace OAI

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝕜 ι κ : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

lemma bracket_diagonal_apply (d : ι → 𝕜) (X : Matrix ι ι 𝕜) (i j : ι) :
    ⁅diagonal d,X⁆ i j = (d i-d j)*X i j := by
  rw [Ring.lie_def,Matrix.sub_apply,diagonal_mul,mul_diagonal]
  ring

/-- A normalized factor of a polynomial in a diagonal adjoint operator. -/
def filterEntry (d : ι → 𝕜) (p q i j : ι) (X : Matrix ι ι 𝕜) : Matrix ι ι 𝕜 :=
    ((d p-d q)-(d i-d j))⁻¹ • (⁅diagonal d,X⁆-(d i-d j) • X)

lemma filterEntry_apply (d : ι → 𝕜) (p q i j a b : ι) (X : Matrix ι ι 𝕜) :
    filterEntry d p q i j X a b =
      ((d p-d q)-(d i-d j))⁻¹*((d a-d b)-(d i-d j))*X a b := by
  simp only [filterEntry,Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply,bracket_diagonal_apply]
  ring

lemma filterEntry_mem (L : LieSubalgebra 𝕜 (Matrix ι ι 𝕜))
    {d : ι → 𝕜} (hd : diagonal d ∈ L) (p q i j : ι)
    {X : Matrix ι ι 𝕜} (hX : X ∈ L) : filterEntry d p q i j X ∈ L :=
  L.smul_mem _ (L.sub_mem (L.lie_mem hd hX) (L.smul_mem _ hX))

/-- Finite joint-eigenvalue interpolation isolates a genuine directed matrix
entry. Zeros of the input require no spectral separation. This is the precise
linear-algebra step used after the torus Fourier projection in the manuscript. -/
theorem isolate_entry (L : LieSubalgebra 𝕜 (Matrix ι ι 𝕜))
    (d : κ → ι → 𝕜) (hd : ∀ a,diagonal (d a) ∈ L)
    {X : Matrix ι ι 𝕜} (hX : X ∈ L) (p q : ι)
    (hsep : ∀ i j, (i,j) ≠ (p,q) → X i j ≠ 0 →
      ∃ a, d a p-d a q ≠ d a i-d a j) :
    single p q (X p q) ∈ L := by
  have construct (s : Finset (ι×ι)) (hs : (p,q) ∉ s) :
      ∃ Z : Matrix ι ι 𝕜, Z ∈ L ∧ Z p q = X p q ∧
        (∀ i j,X i j = 0 → Z i j = 0) ∧ (∀ r ∈ s,Z r.1 r.2 = 0) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨X,hX,rfl,fun _ _ h => h,by simp⟩
    | @insert r s hr ih =>
      obtain ⟨Z,hZ,ht,hz,hsz⟩ := ih (fun h => hs (Finset.mem_insert_of_mem h))
      by_cases hxr : X r.1 r.2 = 0
      · exact ⟨Z,hZ,ht,hz,fun z h => (Finset.mem_insert.1 h).elim
          (fun h => h ▸ hz r.1 r.2 hxr) (hsz z)⟩
      · obtain ⟨a,ha⟩ := hsep r.1 r.2 (by
          intro he; exact hs (he ▸ Finset.mem_insert_self r s)) hxr
        refine ⟨filterEntry (d a) p q r.1 r.2 Z,filterEntry_mem L (hd a) p q _ _ hZ,?_,?_,?_⟩
        · rw [filterEntry_apply,inv_mul_cancel₀ (sub_ne_zero.2 ha),one_mul,ht]
        · intro i j hij
          rw [filterEntry_apply,hz i j hij,mul_zero]
        · intro z hz'
          rcases Finset.mem_insert.1 hz' with rfl | hzs
          · rw [filterEntry_apply,sub_self,mul_zero,zero_mul]
          · rw [filterEntry_apply,hsz z hzs,mul_zero]
  obtain ⟨Z,hZ,ht,_,hz⟩ := construct (Finset.univ.erase (p,q)) (Finset.notMem_erase _ _)
  have he : Z = single p q (X p q) := by
    ext i j
    by_cases hij : (i,j) = (p,q)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hij
      simpa using ht
    · have hs : single p q (X p q) i j = 0 :=
        Matrix.single_apply_of_ne p q (X p q) i j (fun h => hij (Prod.ext h.1.symm h.2.symm))
      exact (hz (i,j) (Finset.mem_erase.2 ⟨hij,Finset.mem_univ _⟩)).trans hs.symm
  exact he ▸ hZ

lemma normalize_entry (L : LieSubalgebra 𝕜 (Matrix ι ι 𝕜))
    {p q : ι} {a : 𝕜} (ha : a ≠ 0) (h : single p q a ∈ L) :
    single p q (1:𝕜) ∈ L := by
  have h' := L.smul_mem a⁻¹ h
  simpa only [smul_single,smul_eq_mul,inv_mul_cancel₀ ha] using h'

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
variable {𝕜 ι : Type*} [Field 𝕜] [CharZero 𝕜]

/-- The joint weight differences of the diagonal quadratic operators are
injective as soon as the shift has three nonzero coordinates. -/
theorem weight_separation (δ v : ι → 𝕜)
    (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : δ a ≠ 0) (hb : δ b ≠ 0) (hc : δ c ≠ 0)
    (h : ∀ i j, i ≠ j → v i * δ j + v j * δ i = 0) : v = 0 := by
  have hab' := h a b hab
  have hac' := h a c hac
  have hbc' := h b c hbc
  have hva : v a = 0 := by
    have he : (2:𝕜) * δ b * δ c * v a = 0 := by
      linear_combination δ c * hab' + δ b * hac' - δ a * hbc'
    exact (mul_eq_zero.1 he).resolve_left
      (mul_ne_zero (mul_ne_zero (by norm_num) hb) hc)
  funext i
  by_cases hi : i = a
  · simpa [hi] using hva
  · have he := h i a hi
    simpa only [hva,zero_mul,add_zero,mul_eq_zero,ha,or_false,Pi.zero_apply] using he

omit [CharZero 𝕜] in
lemma quadratic_weight_difference (ν δ : ι → 𝕜) (i j : ι) :
    (ν i+δ i)*(ν j+δ j)-ν i*ν j =
      ν i*δ j+ν j*δ i+δ i*δ j := by ring

/-- The exact joint eigenvalues in manuscript (control-block-eigenvalues). -/
theorem joint_weight_injective (δ : ι → 𝕜)
    (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : δ a ≠ 0) (hb : δ b ≠ 0) (hc : δ c ≠ 0)
    {ν μ : ι → 𝕜}
    (h : ∀ i j, i ≠ j →
      ν i*δ j+ν j*δ i+δ i*δ j = μ i*δ j+μ j*δ i+δ i*δ j) : ν = μ := by
  have hz := weight_separation δ (ν-μ) a b c hab hac hbc ha hb hc (by
    intro i j hij
    have he := h i j hij
    change (ν i-μ i)*δ j+(ν j-μ j)*δ i = 0
    linear_combination he)
  exact sub_eq_zero.1 hz

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open Matrix
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

lemma bracket_units (a b c : ι) (h : a ≠ c) :
    ⁅single c b (1:𝕜),single b a (1:𝕜)⁆ = single c a 1 := by
  rw [Ring.lie_def,single_mul_single_same,single_mul_single_of_ne (1:𝕜) b a c h (1:𝕜)]
  simp

/-- Nested brackets along a nonreturning directed path produce the endpoint
unit. No associative multiplication closure of the Lie algebra is assumed. -/
theorem unit_mem_of_path (L : LieSubalgebra 𝕜 (Matrix ι ι 𝕜))
    (v : ℕ → ι) (r : ℕ) (hr : 0 < r)
    (hne : ∀ j,0 < j → j ≤ r → v j ≠ v 0)
    (hedge : ∀ j,j < r → single (v (j+1)) (v j) (1:𝕜) ∈ L) :
    single (v r) (v 0) (1:𝕜) ∈ L := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hzero : r = 0
    · subst r
      exact hedge 0 (by omega)
    · have he := hedge r (by omega)
      have hi := ih (by omega) (fun j hj hjr => hne j hj (by omega))
        (fun j hj => hedge j (by omega))
      have hb := L.lie_mem he hi
      rw [bracket_units _ _ _ (hne (r+1) (by omega) (by omega)).symm] at hb
      exact hb

lemma diagonal_difference_mem (L : LieSubalgebra 𝕜 (Matrix ι ι 𝕜))
    {i j : ι} (hij : single i j (1:𝕜) ∈ L)
    (hji : single j i (1:𝕜) ∈ L) : single i i (1:𝕜)-single j j 1 ∈ L := by
  have h := L.lie_mem hij hji
  simpa only [Ring.lie_def,single_mul_single_same,mul_one] using h

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

/-- On the extreme weight layer there is no opposite pair. Equality of torus
weight and total polynomial degree therefore determines the actual monomial,
even among all (not necessarily harmonic) monomials. -/
theorem extreme_weight_unique (d e : ι ⊕ ι → ℕ)
    (he : ∀ i,e (.inl i) = 0 ∨ e (.inr i) = 0)
    (hdeg : ∑ a,d a = ∑ a,e a)
    (hweight : ∀ i,(d (.inl i):ℤ)-d (.inr i) = e (.inl i)-e (.inr i)) : d = e := by
  have hle : ∀ a,e a ≤ d a := by
    intro a
    rcases a with i | i <;> have hw := hweight i <;> rcases he i with h | h <;> omega
  have hsum := (Finset.sum_eq_sum_iff_of_le (fun a (_ : a ∈ Finset.univ) => hle a)).1 hdeg.symm
  exact funext fun a => (hsum a (Finset.mem_univ a)).symm

omit [Fintype ι] in
/-- At a three-coordinate shift, linear torus differences and pairwise
quadratic torus differences distinguish an extreme-to-extreme entry from
EVERY other matrix entry. Thus weight multiplicities in the interior cannot
silently turn a block into a rank-one operator. -/
theorem extreme_joint_separation
    {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]
    {μ : Type*} (w : μ → ι → 𝕜) (p q : μ)
    (hp : ∀ x,w x = w p → x = p) (hq : ∀ x,w x = w q → x = q)
    (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : w p a-w q a ≠ 0) (hb : w p b-w q b ≠ 0) (hc : w p c-w q c ≠ 0)
    (x y : μ) (hxy : (x,y) ≠ (p,q)) :
    (∃ i,w p i-w q i ≠ w x i-w y i) ∨
    ∃ i j,i ≠ j ∧ w p i*w p j-w q i*w q j ≠ w x i*w x j-w y i*w y j := by
  by_contra! h
  have hδ : w x = w y+(w p-w q) := by
    funext i
    have ht := h.1 i
    change w x i = w y i+(w p i-w q i)
    linear_combination -ht
  have hpδ : w p = w q+(w p-w q) := by abel
  have hy : w y = w q := by
    apply joint_weight_injective (w p-w q) a b c hab hac hbc ha hb hc
    intro i j hij
    have ht := h.2 i j hij
    rw [hδ,hpδ] at ht
    simp only [Pi.add_apply,Pi.sub_apply] at ht ⊢
    linear_combination -ht
  exact hxy (Prod.ext (hp x (by rw [hδ,hy,← hpδ])) (hq y hy))

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
variable {𝕜 ι κ : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]
attribute [local instance 100] LieRing.ofAssociativeRing
open Matrix
lemma filterEntry_mem_normalizer (L : LieSubalgebra 𝕜 (Matrix ι ι 𝕜))
    {d : ι → 𝕜} (hd : ∀ X ∈ L, ⁅diagonal d,X⁆ ∈ L) (p q i j : ι)
    {X : Matrix ι ι 𝕜} (hX : X ∈ L) : filterEntry d p q i j X ∈ L :=
  L.smul_mem _ (L.sub_mem (hd X hX) (L.smul_mem _ hX))

/-- Finite joint-eigenvalue interpolation isolates a genuine directed matrix
entry. Zeros of the input require no spectral separation. This is the precise
linear-algebra step used after the torus Fourier projection in the manuscript. -/
theorem isolate_entry_normalizers (L : LieSubalgebra 𝕜 (Matrix ι ι 𝕜))
    (d : κ → ι → 𝕜) (hd : ∀ a X, X ∈ L → ⁅diagonal (d a),X⁆ ∈ L)
    {X : Matrix ι ι 𝕜} (hX : X ∈ L) (p q : ι)
    (hsep : ∀ i j, (i,j) ≠ (p,q) → X i j ≠ 0 →
      ∃ a, d a p-d a q ≠ d a i-d a j) :
    single p q (X p q) ∈ L := by
  have construct (s : Finset (ι×ι)) (hs : (p,q) ∉ s) :
      ∃ Z : Matrix ι ι 𝕜, Z ∈ L ∧ Z p q = X p q ∧
        (∀ i j,X i j = 0 → Z i j = 0) ∧ (∀ r ∈ s,Z r.1 r.2 = 0) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨X,hX,rfl,fun _ _ h => h,by simp⟩
    | @insert r s hr ih =>
      obtain ⟨Z,hZ,ht,hz,hsz⟩ := ih (fun h => hs (Finset.mem_insert_of_mem h))
      by_cases hxr : X r.1 r.2 = 0
      · exact ⟨Z,hZ,ht,hz,fun z h => (Finset.mem_insert.1 h).elim
          (fun h => h ▸ hz r.1 r.2 hxr) (hsz z)⟩
      · obtain ⟨a,ha⟩ := hsep r.1 r.2 (by
          intro he; exact hs (he ▸ Finset.mem_insert_self r s)) hxr
        refine ⟨filterEntry (d a) p q r.1 r.2 Z,filterEntry_mem_normalizer L (hd a) p q _ _ hZ,?_,?_,?_⟩
        · rw [filterEntry_apply,inv_mul_cancel₀ (sub_ne_zero.2 ha),one_mul,ht]
        · intro i j hij
          rw [filterEntry_apply,hz i j hij,mul_zero]
        · intro z hz'
          rcases Finset.mem_insert.1 hz' with rfl | hzs
          · rw [filterEntry_apply,sub_self,mul_zero,zero_mul]
          · rw [filterEntry_apply,hsz z hzs,mul_zero]
  obtain ⟨Z,hZ,ht,_,hz⟩ := construct (Finset.univ.erase (p,q)) (Finset.notMem_erase _ _)
  have he : Z = single p q (X p q) := by
    ext i j
    by_cases hij : (i,j) = (p,q)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hij
      simpa using ht
    · have hs : single p q (X p q) i j = 0 :=
        Matrix.single_apply_of_ne p q (X p q) i j (fun h => hij (Prod.ext h.1.symm h.2.symm))
      exact (hz (i,j) (Finset.mem_erase.2 ⟨hij,Finset.mem_univ _⟩)).trans hs.symm
  exact he ▸ hZ


end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open Matrix MvPolynomial HarmonicCounterexample.Berger
open HarmonicCounterexample.Berger.ComplexStructure
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing
variable {s l : ℕ}

def ExtremeMonomial (ν : MonomialIndex (Fin s ⊕ Fin s) l) : Prop :=
  ∀ i,ν.1 (.inl i) = 0 ∨ ν.1 (.inr i) = 0

lemma extreme_monomial_weight_unique (ν : MonomialIndex (Fin s ⊕ Fin s) l)
    (hν : ExtremeMonomial ν) (μ : MonomialIndex (Fin s ⊕ Fin s) l)
    (hw : monomialWeight μ.1 = monomialWeight ν.1) : μ = ν := by
  apply Subtype.ext
  apply DFunLike.ext'
  apply extreme_weight_unique (fun a => μ.1 a) (fun a => ν.1 a) hν
  · have hm : μ.1.degree = ∑ a,μ.1 a := Finsupp.sum_fintype μ.1 (fun _ a => a) (fun _ => rfl)
    have hn : ν.1.degree = ∑ a,ν.1 a := Finsupp.sum_fintype ν.1 (fun _ a => a) (fun _ => rfl)
    rw [← hm,← hn,μ.2,ν.2]
  · intro i
    have hi := congrFun hw i
    change (μ.1 (.inl i):ℂ)-μ.1 (.inr i) = (ν.1 (.inl i):ℂ)-ν.1 (.inr i) at hi
    exact_mod_cast hi

/-- Every nonzero actual extreme-to-extreme coefficient at a shift with three
nonzero coordinates yields a matrix unit in the actual angular Lie algebra. -/
theorem angularLie_extreme_entry
    (X : Matrix (MonomialIndex (Fin s ⊕ Fin s) l) (MonomialIndex (Fin s ⊕ Fin s) l) ℂ)
    (hX : X ∈ angularLie l) (μ ν : MonomialIndex (Fin s ⊕ Fin s) l)
    (hμ : ExtremeMonomial μ) (hν : ExtremeMonomial ν)
    (a b c : Fin s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : monomialWeight μ.1 a-monomialWeight ν.1 a ≠ 0)
    (hb : monomialWeight μ.1 b-monomialWeight ν.1 b ≠ 0)
    (hc : monomialWeight μ.1 c-monomialWeight ν.1 c ≠ 0)
    (he : X μ ν ≠ 0) : single μ ν (1:ℂ) ∈ angularLie l := by
  let d : Fin s ⊕ {ij : Fin s × Fin s // ij.1 ≠ ij.2} →
      MonomialIndex (Fin s ⊕ Fin s) l → ℂ := Sum.elim
    (fun i p => monomialWeight p.1 i)
    (fun ij p => monomialWeight p.1 ij.1.1*monomialWeight p.1 ij.1.2)
  have hd : ∀ i Z,Z ∈ angularLie (s := s) l → ⁅diagonal (d i),Z⁆ ∈ angularLie l := by
    rintro (i | ij) Z hZ
    · exact angularLie_weight_normalizer l i Z hZ
    · exact angularLie_pair_normalizer l ij.1.1 ij.1.2 ij.2 Z hZ
  apply normalize_entry (angularLie l) he
  apply isolate_entry_normalizers (angularLie l) d hd hX μ ν
  intro p q hpq _
  have hs := extreme_joint_separation (fun p : MonomialIndex (Fin s ⊕ Fin s) l =>
    monomialWeight p.1) μ ν (extreme_monomial_weight_unique μ hμ)
    (extreme_monomial_weight_unique ν hν) a b c hab hac hbc ha hb hc p q hpq
  rcases hs with ⟨i,hi⟩ | ⟨i,j,hij,hij'⟩
  · exact ⟨.inl i,hi⟩
  · exact ⟨.inr ⟨(i,j),hij⟩,hij'⟩

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open Finsupp
variable {ι : Type*} [DecidableEq ι]

/-- Exponents of a genuine term in the second-order polynomial field. -/
def secondExponent (ν : ι →₀ ℕ) (a b c d : ι) : ι →₀ ℕ :=
  single c 1+single d 1+(ν-single a 1-single b 1)

/-- A deficit of two forces both differentiated variables. Natural truncated
subtraction is handled rather than tacitly converted to a Laurent model. -/
lemma split_forces_derivatives (ν : ι →₀ ℕ) (i j k a b c d : ι)
    (hn : 2 ≤ ν i) (hij : i ≠ j) (hik : i ≠ k)
    (he : secondExponent ν a b c d = secondExponent ν i i j k) : a = i ∧ b = i := by
  have h := congrArg (fun f : ι →₀ ℕ => f i) he
  by_cases ha : a = i <;> by_cases hb : b = i
  · exact ⟨ha,hb⟩
  all_goals
    simp only [secondExponent,Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_apply,
      ite_eq_right hij.symm,ite_eq_right hik.symm,ha,hb,ite_true,ite_false,zero_add,
      Nat.sub_zero] at h
    omega

/-- Once the differentiated variables are known, the increment at two distinct
coordinates forces precisely the two ordered replacements. -/
lemma split_forces_replacements (ν : ι →₀ ℕ) (i j k c d : ι)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (he : secondExponent ν i i c d = secondExponent ν i i j k) :
    (c = j ∧ d = k) ∨ (c = k ∧ d = j) := by
  have h₁ := congrArg (fun f : ι →₀ ℕ => f j) he
  have h₂ := congrArg (fun f : ι →₀ ℕ => f k) he
  simp only [secondExponent,Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_apply,
    ite_eq_right hij,ite_eq_right hik,ite_eq_right hjk,ite_eq_right hjk.symm,Nat.sub_zero] at h₁ h₂
  by_cases hcj : c = j <;> by_cases hck : c = k <;>
    by_cases hdj : d = j <;> by_cases hdk : d = k
  all_goals simp only [hcj,hck,hdj,hdk,hjk,hjk.symm,ite_true,ite_false] at h₁ h₂
  all_goals first | exact Or.inl ⟨hcj,hdk⟩ | exact Or.inr ⟨hck,hdj⟩ | (exfalso; apply hjk; exact hcj.symm.trans hck) | (exfalso; apply hjk; exact hdj.symm.trans hdk) | omega

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open scoped BigOperators
open Matrix MvPolynomial Finsupp
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

/-- The genuine second-order contribution, with every ordered differentiation
and replacement included. -/
def secondField (M : Matrix ι ι 𝕜) (P : MvPolynomial ι 𝕜) : MvPolynomial ι 𝕜 :=
  ∑ a : ι, ∑ c : ι, ∑ b : ι, ∑ d : ι,
    (M a c*M b d) • (X c*X d*pderiv b (pderiv a P))

lemma linearField_square_second (M : Matrix ι ι 𝕜) (P : MvPolynomial ι 𝕜) :
    linearField M (linearField M P) = linearField (M*M) P+secondField M P := by
  rw [linearField_square]
  congr 1
  simp only [secondField,linearField_apply,Finset.mul_sum,Finset.smul_sum,
    mul_smul_comm,smul_smul,mul_assoc]

omit [DecidableEq ι] in
lemma secondField_monomial (M : Matrix ι ι 𝕜) (ν : ι →₀ ℕ) :
    secondField M (monomial ν 1) =
      ∑ a : ι, ∑ c : ι, ∑ b : ι, ∑ d : ι,
        monomial (secondExponent ν a b c d)
          (M a c*M b d*((ν a:𝕜)*(((ν-single a 1 : ι →₀ ℕ) b):𝕜))) := by
  simp only [secondField,pderiv_monomial,X,monomial_mul_monomial,smul_monomial,
    smul_eq_mul,one_mul,mul_one,secondExponent,mul_assoc]

lemma secondField_coeff (M : Matrix ι ι 𝕜) (ν μ : ι →₀ ℕ) :
    (secondField M (monomial ν 1)).coeff μ =
      ∑ a : ι, ∑ c : ι, ∑ b : ι, ∑ d : ι,
        if secondExponent ν a b c d = μ then
          M a c*M b d*((ν a:𝕜)*(((ν-Finsupp.single a 1 : ι →₀ ℕ) b):𝕜)) else 0 := by
  simp only [secondField_monomial,coeff_sum,coeff_monomial]

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open scoped BigOperators
open Matrix MvPolynomial Finsupp
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma secondExponent_split_iff (ν : ι →₀ ℕ) (i j k a b c d : ι)
    (hn : 2 ≤ ν i) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    secondExponent ν a b c d = secondExponent ν i i j k ↔
      a = i ∧ b = i ∧ ((c = j ∧ d = k) ∨ (c = k ∧ d = j)) := by
  constructor
  · intro h
    obtain ⟨ha,hb⟩ := split_forces_derivatives ν i j k a b c d hn hij hik h
    subst a; subst b
    exact ⟨rfl,rfl,split_forces_replacements ν i j k c d hij hik hjk h⟩
  · rintro ⟨rfl,rfl,(⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩
    · rfl
    · simp only [secondExponent,add_comm]

lemma secondField_split_coeff (M : Matrix ι ι 𝕜) (ν : ι →₀ ℕ) (i j k : ι)
    (hn : 2 ≤ ν i) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (secondField M (monomial ν 1)).coeff (secondExponent ν i i j k) =
      2*M i j*M i k*(ν i:𝕜)*((ν i-1:ℕ):𝕜) := by
  rw [secondField_coeff]
  have he (a c b d : ι) :
      (if secondExponent ν a b c d = secondExponent ν i i j k then
        M a c*M b d*((ν a:𝕜)*(((ν-Finsupp.single a 1 : ι →₀ ℕ) b):𝕜)) else 0) =
      (if a = i then if b = i then
        (if c = j then if d = k then M i j*M i k*((ν i:𝕜)*((ν i-1:ℕ):𝕜)) else 0 else 0)+
        (if c = k then if d = j then M i k*M i j*((ν i:𝕜)*((ν i-1:ℕ):𝕜)) else 0 else 0)
       else 0 else 0) := by
    simp only [secondExponent_split_iff ν i j k a b c d hn hij hik hjk]
    by_cases ha : a = i
    · subst a
      by_cases hb : b = i
      · subst b
        by_cases hcj : c = j <;> by_cases hck : c = k <;>
          by_cases hdj : d = j <;> by_cases hdk : d = k
        all_goals simp_all [Finsupp.tsub_apply]
      · simp [hb]
    · simp [ha]
  simp_rw [he]
  simp only [Finset.sum_ite_irrel,Finset.sum_add_distrib,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,Finset.sum_const_zero]
  ring

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open scoped BigOperators
open Matrix MvPolynomial Finsupp
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma merge_forces_derivatives (ν : ι →₀ ℕ) (i j k a b c d : ι)
    (hj : 1 ≤ ν j) (hk : 1 ≤ ν k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (he : secondExponent ν a b c d = secondExponent ν j k i i) :
    (a = j ∧ b = k) ∨ (a = k ∧ b = j) := by
  have hj' : a = j ∨ b = j := by
    by_contra! h
    have ht := congrArg (fun f : ι →₀ ℕ => f j) he
    simp only [secondExponent,Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_apply,
      ite_eq_right hij,ite_eq_right hjk.symm,ite_eq_right h.1,ite_eq_right h.2,ite_true,zero_add,Nat.sub_zero] at ht
    omega
  have hk' : a = k ∨ b = k := by
    by_contra! h
    have ht := congrArg (fun f : ι →₀ ℕ => f k) he
    simp only [secondExponent,Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_apply,
      ite_eq_right hik,ite_eq_right hjk,ite_eq_right h.1,ite_eq_right h.2,ite_true,zero_add,Nat.sub_zero] at ht
    omega
  rcases hj' with ha | hb <;> rcases hk' with ha' | hb'
  · exact (hjk (ha.symm.trans ha')).elim
  · exact Or.inl ⟨ha,hb'⟩
  · exact Or.inr ⟨ha',hb⟩
  · exact (hjk (hb.symm.trans hb')).elim

omit [Fintype ι] in
lemma merge_forces_replacements (ν : ι →₀ ℕ) (i j k c d : ι)
    (he : secondExponent ν j k c d = secondExponent ν j k i i) : c = i ∧ d = i := by
  have h : single c 1+single d 1 = (single i 1+single i 1 : ι →₀ ℕ) := add_right_cancel he
  have ht := congrArg (fun f : ι →₀ ℕ => f i) h
  simp only [Finsupp.add_apply,Finsupp.single_apply,ite_true] at ht
  by_cases hc : c = i <;> by_cases hd : d = i
  · exact ⟨hc,hd⟩
  all_goals simp only [hc,hd,ite_true,ite_false] at ht
  all_goals omega

omit [Fintype ι] in
lemma secondExponent_merge_iff (ν : ι →₀ ℕ) (i j k a b c d : ι)
    (hj : 1 ≤ ν j) (hk : 1 ≤ ν k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    secondExponent ν a b c d = secondExponent ν j k i i ↔
      ((a = j ∧ b = k) ∨ (a = k ∧ b = j)) ∧ c = i ∧ d = i := by
  have hs (c d : ι) : secondExponent ν k j c d = secondExponent ν j k c d := by
    simp only [secondExponent,tsub_tsub,add_comm (single k 1) (single j 1)]
  constructor
  · intro h
    have hd := merge_forces_derivatives ν i j k a b c d hj hk hij hik hjk h
    refine ⟨hd,?_⟩
    rcases hd with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · subst a; subst b; exact merge_forces_replacements ν i j k c d h
    · subst a; subst b; exact merge_forces_replacements ν i j k c d (by rwa [hs] at h)
  · rintro ⟨(⟨ha,hb⟩ | ⟨ha,hb⟩),hc,hd⟩
    · subst a; subst b; subst c; subst d; rfl
    · subst a; subst b; subst c; subst d; exact hs _ _

lemma secondField_merge_coeff (M : Matrix ι ι 𝕜) (ν : ι →₀ ℕ) (i j k : ι)
    (hj : 1 ≤ ν j) (hk : 1 ≤ ν k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (secondField M (monomial ν 1)).coeff (secondExponent ν j k i i) =
      2*M j i*M k i*(ν j:𝕜)*(ν k:𝕜) := by
  rw [secondField_coeff]
  have he (a c b d : ι) :
      (if secondExponent ν a b c d = secondExponent ν j k i i then
        M a c*M b d*((ν a:𝕜)*(((ν-Finsupp.single a 1 : ι →₀ ℕ) b):𝕜)) else 0) =
      (if a = j then if b = k then if c = i then if d = i then
        M j i*M k i*((ν j:𝕜)*(ν k:𝕜)) else 0 else 0 else 0 else 0)+
      (if a = k then if b = j then if c = i then if d = i then
        M k i*M j i*((ν k:𝕜)*(ν j:𝕜)) else 0 else 0 else 0 else 0) := by
    simp only [secondExponent_merge_iff ν i j k a b c d hj hk hij hik hjk]
    by_cases hc : c = i <;> by_cases hd : d = i
    all_goals simp only [hc,hd,and_true,and_false,↓reduceIte]
    all_goals try simp
    by_cases haj : a = j <;> by_cases hak : a = k <;>
      by_cases hbj : b = j <;> by_cases hbk : b = k
    all_goals simp_all
  simp_rw [he]
  simp only [Finset.sum_ite_irrel,Finset.sum_add_distrib,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,Finset.sum_const_zero]
  ring

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open scoped BigOperators
open MvPolynomial Finsupp
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma split_exponent_ne (ν : ι →₀ ℕ) (i j k : ι)
    (hn : 2 ≤ ν i) (hij : i ≠ j) (hik : i ≠ k) :
    secondExponent ν i i j k ≠ ν := by
  intro h
  have ht := congrArg (fun f : ι →₀ ℕ => f i) h
  simp only [secondExponent,Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_apply,
    ite_eq_right hij.symm,ite_eq_right hik.symm,ite_true,zero_add] at ht
  omega

omit [Fintype ι] in
lemma merge_exponent_ne (ν : ι →₀ ℕ) (i j k : ι)
    (hj : 1 ≤ ν j) (hij : i ≠ j) (hjk : j ≠ k) :
    secondExponent ν j k i i ≠ ν := by
  intro h
  have ht := congrArg (fun f : ι →₀ ℕ => f j) h
  simp only [secondExponent,Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_apply,
    ite_eq_right hij,ite_eq_right hjk.symm,ite_true,zero_add,Nat.sub_zero] at ht
  omega

lemma fieldSquare_split_coeff (M : Matrix ι ι 𝕜) (hM : M*M = -1)
    {l : ℕ} (ν : ι →₀ ℕ) (hν : (monomial ν (1:𝕜)).IsHomogeneous l) (i j k : ι)
    (hn : 2 ≤ ν i) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (linearField M (linearField M (monomial ν 1))).coeff (secondExponent ν i i j k) =
      2*M i j*M i k*(ν i:𝕜)*((ν i-1:ℕ):𝕜) := by
  rw [linearField_square_second,hM,linearField_neg_one _ hν,
    AddMonoidAlgebra.coeff_add,Finsupp.add_apply,coeff_smul,
    coeff_monomial,ite_eq_right (split_exponent_ne ν i j k hn hij hik).symm]
  simp only [smul_zero,zero_add,secondField_split_coeff M ν i j k hn hij hik hjk]

lemma fieldSquare_merge_coeff (M : Matrix ι ι 𝕜) (hM : M*M = -1)
    {l : ℕ} (ν : ι →₀ ℕ) (hν : (monomial ν (1:𝕜)).IsHomogeneous l) (i j k : ι)
    (hj : 1 ≤ ν j) (hk : 1 ≤ ν k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (linearField M (linearField M (monomial ν 1))).coeff (secondExponent ν j k i i) =
      2*M j i*M k i*(ν j:𝕜)*(ν k:𝕜) := by
  rw [linearField_square_second,hM,linearField_neg_one _ hν,
    AddMonoidAlgebra.coeff_add,Finsupp.add_apply,coeff_smul,
    coeff_monomial,ite_eq_right (merge_exponent_ne ν i j k hj hij hjk).symm]
  simp only [smul_zero,zero_add,secondField_merge_coeff M ν i j k hj hk hij hik hjk]

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open Matrix MvPolynomial HarmonicCounterexample.Berger
open HarmonicCounterexample.Berger.ComplexStructure
open scoped BigOperators
variable {s l : ℕ}

lemma signedIndex_ne {i j : Fin s} (h : i ≠ j) (ε β : Bool) :
    signedIndex i ε ≠ signedIndex j β := by
  cases ε <;> cases β <;> simp [signedIndex,h]

lemma coordinateSign_ne_zero (a : Fin s ⊕ Fin s) : coordinateSign a ≠ 0 := by
  rcases a with i | i <;> simp [coordinateSign]

lemma traceFree_offdiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {i j : ι} (h : i ≠ j) : traceFree A i j = A i j := by
  simp [traceFree,h]

lemma angularSquare_entry (J : ComplexStructure (Fin s ⊕ Fin s))
    (μ ν : MonomialIndex (Fin s ⊕ Fin s) l) :
    (angularRepresentation l J.matrix*angularRepresentation l J.matrix) μ ν =
      (linearField (splitMatrix J) (linearField (splitMatrix J) (monomial ν.1 1))).coeff μ.1 := by
  change (homogeneousMatrix l (splitFieldMatrix J.matrix)*
    homogeneousMatrix l (splitFieldMatrix J.matrix)) μ ν = _
  rw [splitFieldMatrix_complex,homogeneousMatrix_square_apply]

/-- The manuscript's actual split coefficient. Its nonvanishing is not an
assumption about a spectral surrogate. -/
lemma angularSquare_split_coefficient (i j k : Fin s)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (ε β γ : Bool)
    (μ ν : MonomialIndex (Fin s ⊕ Fin s) l)
    (hn : 2 ≤ ν.1 (signedIndex i ε))
    (hμ : μ.1 = secondExponent ν.1 (signedIndex i ε) (signedIndex i ε)
      (signedIndex j β) (signedIndex k γ)) :
    traceFree (angularRepresentation l (triple i j k).matrix*
      angularRepresentation l (triple i j k).matrix) μ ν =
      Complex.I*coordinateSign (signedIndex i ε)/2*
        (ν.1 (signedIndex i ε):ℂ)*((ν.1 (signedIndex i ε)-1:ℕ):ℂ) := by
  have hi := signedIndex_ne hij ε β
  have hk := signedIndex_ne hik ε γ
  have hj := signedIndex_ne hjk β γ
  have hne : μ ≠ ν := by
    intro h
    have he := congrArg Subtype.val h
    rw [hμ] at he
    exact split_exponent_ne ν.1 _ _ _ hn hi hk he
  rw [traceFree_offdiagonal _ hne,angularSquare_entry,hμ,
    fieldSquare_split_coeff _ (splitMatrix_square _) ν.1
      (isHomogeneous_monomial (1:ℂ) ν.2) _ _ _ hn hi hk hj,
    triple_split_ij i j k hij hik hjk ε β,triple_split_ik i j k hij hik hjk ε γ]
  ring

lemma angularSquare_split_nonzero (i j k : Fin s)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (ε β γ : Bool)
    (μ ν : MonomialIndex (Fin s ⊕ Fin s) l)
    (hn : 2 ≤ ν.1 (signedIndex i ε))
    (hμ : μ.1 = secondExponent ν.1 (signedIndex i ε) (signedIndex i ε)
      (signedIndex j β) (signedIndex k γ)) :
    traceFree (angularRepresentation l (triple i j k).matrix*
      angularRepresentation l (triple i j k).matrix) μ ν ≠ 0 := by
  rw [angularSquare_split_coefficient i j k hij hik hjk ε β γ μ ν hn hμ]
  exact mul_ne_zero (mul_ne_zero (div_ne_zero
    (mul_ne_zero Complex.I_ne_zero (coordinateSign_ne_zero _)) (by norm_num))
      (Nat.cast_ne_zero.2 (by omega))) (Nat.cast_ne_zero.2 (by omega))

lemma angularSquare_merge_coefficient (i j k : Fin s)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (ε β γ : Bool)
    (μ ν : MonomialIndex (Fin s ⊕ Fin s) l)
    (hnj : 1 ≤ ν.1 (signedIndex j β)) (hnk : 1 ≤ ν.1 (signedIndex k γ))
    (hμ : μ.1 = secondExponent ν.1 (signedIndex j β) (signedIndex k γ)
      (signedIndex i ε) (signedIndex i ε)) :
    traceFree (angularRepresentation l (triple i j k).matrix*
      angularRepresentation l (triple i j k).matrix) μ ν =
      -Complex.I*coordinateSign (signedIndex i ε)/2*
        (ν.1 (signedIndex j β):ℂ)*(ν.1 (signedIndex k γ):ℂ) := by
  have hi := signedIndex_ne hij ε β
  have hk := signedIndex_ne hik ε γ
  have hj := signedIndex_ne hjk β γ
  have hne : μ ≠ ν := by
    intro h
    have he := congrArg Subtype.val h
    rw [hμ] at he
    exact merge_exponent_ne ν.1 _ _ _ hnj hi hj he
  rw [traceFree_offdiagonal _ hne,angularSquare_entry,hμ,
    fieldSquare_merge_coeff _ (splitMatrix_square _) ν.1
      (isHomogeneous_monomial (1:ℂ) ν.2) _ _ _ hnj hnk hi hk hj,
    triple_split_ji i j k hij hik hjk ε β,triple_split_ki i j k hij hik hjk ε γ]
  ring

lemma angularSquare_merge_nonzero (i j k : Fin s)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (ε β γ : Bool)
    (μ ν : MonomialIndex (Fin s ⊕ Fin s) l)
    (hnj : 1 ≤ ν.1 (signedIndex j β)) (hnk : 1 ≤ ν.1 (signedIndex k γ))
    (hμ : μ.1 = secondExponent ν.1 (signedIndex j β) (signedIndex k γ)
      (signedIndex i ε) (signedIndex i ε)) :
    traceFree (angularRepresentation l (triple i j k).matrix*
      angularRepresentation l (triple i j k).matrix) μ ν ≠ 0 := by
  rw [angularSquare_merge_coefficient i j k hij hik hjk ε β γ μ ν hnj hnk hμ]
  exact mul_ne_zero (mul_ne_zero (div_ne_zero
    (mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) (coordinateSign_ne_zero _)) (by norm_num))
      (Nat.cast_ne_zero.2 (by omega))) (Nat.cast_ne_zero.2 (by omega))

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open Matrix MvPolynomial HarmonicCounterexample.Berger
open HarmonicCounterexample.Berger.ComplexStructure
open scoped BigOperators
variable {s l : ℕ}

lemma monomialWeight_eq_int {μ ν : Fin s ⊕ Fin s →₀ ℕ} {a : Fin s}
    (h : monomialWeight μ a = monomialWeight ν a) :
    (μ (.inl a):ℤ)-μ (.inr a) = (ν (.inl a):ℤ)-ν (.inr a) := by
  unfold monomialWeight at h
  exact_mod_cast h

lemma split_three_weight_shifts (i j k : Fin s)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (ε β γ : Bool)
    (μ ν : MonomialIndex (Fin s ⊕ Fin s) l)
    (hn : 2 ≤ ν.1 (signedIndex i ε))
    (hμ : μ.1 = secondExponent ν.1 (signedIndex i ε) (signedIndex i ε)
      (signedIndex j β) (signedIndex k γ)) :
    (monomialWeight μ.1 i-monomialWeight ν.1 i ≠ 0) ∧
    (monomialWeight μ.1 j-monomialWeight ν.1 j ≠ 0) ∧
    (monomialWeight μ.1 k-monomialWeight ν.1 k ≠ 0) := by
  refine ⟨?_,?_,?_⟩
  all_goals
    intro h
    have ht := monomialWeight_eq_int (sub_eq_zero.1 h)
    rw [hμ] at ht
    cases ε <;> cases β <;> cases γ
    all_goals
      simp only [signedIndex,Bool.false_eq_true,ite_false,ite_true,
        secondExponent,Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_apply,
        Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,
        hij,hik,hjk,hij.symm,hik.symm,hjk.symm,ite_false,ite_true,
        zero_add,add_zero,Nat.sub_zero] at ht hn
      omega

lemma merge_three_weight_shifts (i j k : Fin s)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (ε β γ : Bool)
    (μ ν : MonomialIndex (Fin s ⊕ Fin s) l)
    (hnj : 1 ≤ ν.1 (signedIndex j β)) (hnk : 1 ≤ ν.1 (signedIndex k γ))
    (hμ : μ.1 = secondExponent ν.1 (signedIndex j β) (signedIndex k γ)
      (signedIndex i ε) (signedIndex i ε)) :
    (monomialWeight μ.1 i-monomialWeight ν.1 i ≠ 0) ∧
    (monomialWeight μ.1 j-monomialWeight ν.1 j ≠ 0) ∧
    (monomialWeight μ.1 k-monomialWeight ν.1 k ≠ 0) := by
  refine ⟨?_,?_,?_⟩
  all_goals
    intro h
    have ht := monomialWeight_eq_int (sub_eq_zero.1 h)
    rw [hμ] at ht
    cases ε <;> cases β <;> cases γ
    all_goals
      simp only [signedIndex,Bool.false_eq_true,ite_false,ite_true,
        secondExponent,Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_apply,
        Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,
        hij,hik,hjk,hij.symm,hik.symm,hjk.symm,ite_false,ite_true,
        zero_add,add_zero,Nat.sub_zero] at ht hnj hnk
      omega

/-- Both directions of each legal token split are genuinely generated by squared
orthogonal complex structures. Endpoints are actual homogeneous monomials. -/
theorem angularLie_legal_split (i j k : Fin s)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (ε β γ : Bool)
    (μ ν : MonomialIndex (Fin s ⊕ Fin s) l)
    (hexμ : ExtremeMonomial μ) (hexν : ExtremeMonomial ν)
    (hn : 2 ≤ ν.1 (signedIndex i ε))
    (hμ : μ.1 = secondExponent ν.1 (signedIndex i ε) (signedIndex i ε)
      (signedIndex j β) (signedIndex k γ)) :
    single μ ν (1:ℂ) ∈ angularLie l := by
  obtain ⟨ha,hb,hc⟩ := split_three_weight_shifts i j k hij hik hjk ε β γ μ ν hn hμ
  exact angularLie_extreme_entry _ (angularLie_generator l (triple i j k)) μ ν hexμ hexν
    i j k hij hik hjk ha hb hc
    (angularSquare_split_nonzero i j k hij hik hjk ε β γ μ ν hn hμ)

theorem angularLie_legal_merge (i j k : Fin s)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (ε β γ : Bool)
    (μ ν : MonomialIndex (Fin s ⊕ Fin s) l)
    (hexμ : ExtremeMonomial μ) (hexν : ExtremeMonomial ν)
    (hnj : 1 ≤ ν.1 (signedIndex j β)) (hnk : 1 ≤ ν.1 (signedIndex k γ))
    (hμ : μ.1 = secondExponent ν.1 (signedIndex j β) (signedIndex k γ)
      (signedIndex i ε) (signedIndex i ε)) :
    single μ ν (1:ℂ) ∈ angularLie l := by
  obtain ⟨ha,hb,hc⟩ := merge_three_weight_shifts i j k hij hik hjk ε β γ μ ν hnj hnk hμ
  exact angularLie_extreme_entry _ (angularLie_generator l (triple i j k)) μ ν hexμ hexν
    i j k hij hik hjk ha hb hc
    (angularSquare_merge_nonzero i j k hij hik hjk ε β γ μ ν hnj hnk hμ)

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open Matrix MvPolynomial HarmonicCounterexample.Berger
open HarmonicCounterexample.Berger.ComplexStructure
open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The explicit manuscript token branch, specialized to the n=16 witness. -/
def branchExponent (ε : Bool) (h r t : ℕ) : Fin 8 ⊕ Fin 8 →₀ ℕ :=
  Finsupp.single (signedIndex 0 ε) (2*(h-t)+r)+Finsupp.single (.inl 1) t+Finsupp.single (.inl 2) t

lemma branchExponent_degree (ε : Bool) (h r t : ℕ) (ht : t ≤ h) :
    (branchExponent ε h r t).degree = 2*h+r := by
  simp only [branchExponent,map_add,Finsupp.degree_single]
  omega

def branchMonomial (ε : Bool) (h r t : ℕ) (ht : t ≤ h) :
    MonomialIndex (Fin 8 ⊕ Fin 8) (2*h+r) :=
  ⟨branchExponent ε h r t,branchExponent_degree ε h r t ht⟩

lemma branchMonomial_extreme (ε : Bool) (h r t : ℕ) (ht : t ≤ h) :
    ExtremeMonomial (branchMonomial ε h r t ht) := by
  intro a
  cases ε
  · by_cases ha : a = 0
    · left
      subst a
      norm_num [branchMonomial,branchExponent,signedIndex,Finsupp.single_apply,Fin.ext_iff,Sum.inr_ne_inl]
    · right
      simp [branchMonomial,branchExponent,signedIndex,ha,eq_comm]
  · right
    simp [branchMonomial,branchExponent,signedIndex]

lemma branchMonomial_coordinate (ε : Bool) (h r t : ℕ) (ht : t ≤ h) :
    (branchMonomial ε h r t ht).1 (.inl 1) = t := by
  cases ε <;> norm_num [branchMonomial,branchExponent,signedIndex,Finsupp.single_apply,Fin.ext_iff,Sum.inr_ne_inl]

lemma branchMonomial_distinct (ε : Bool) (h r a b : ℕ) (ha : a ≤ h) (hb : b ≤ h)
    (hab : a ≠ b) : branchMonomial ε h r a ha ≠ branchMonomial ε h r b hb := by
  intro he
  have hh := congrArg (fun p : MonomialIndex (Fin 8 ⊕ Fin 8) (2*h+r) => p.1 (.inl 1)) he
  rw [branchMonomial_coordinate,branchMonomial_coordinate] at hh
  exact hab hh

lemma branchMonomial_pair_count (ε : Bool) (h r t : ℕ) (ht : t < h) :
    2 ≤ (branchMonomial ε h r t (Nat.le_of_lt ht)).1 (signedIndex 0 ε) := by
  cases ε <;> norm_num [branchMonomial,branchExponent,signedIndex,Finsupp.single_apply,Fin.ext_iff,Sum.inr_ne_inl]
  all_goals omega

lemma branchMonomial_split (ε : Bool) (h r t : ℕ) (ht : t < h) :
    (branchMonomial ε h r (t+1) ht).1 =
      secondExponent (branchMonomial ε h r t (Nat.le_of_lt ht)).1
        (signedIndex 0 ε) (signedIndex 0 ε) (.inl 1) (.inl 2) := by
  ext a
  rcases a with a | a
  all_goals
    cases ε <;> by_cases ha : a = 0 <;> by_cases hb : a = 1 <;> by_cases hc : a = 2
    all_goals
      simp_all only [branchMonomial,branchExponent,secondExponent,signedIndex,
        Bool.false_eq_true,ite_false,ite_true,Finsupp.add_apply,Finsupp.tsub_apply,
        Finsupp.single_apply,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,
        eq_comm,ite_false,ite_true,zero_add,add_zero,Nat.sub_zero] <;> omega

lemma branchMonomial_merge (ε : Bool) (h r t : ℕ) (ht : t < h) :
    (branchMonomial ε h r t (Nat.le_of_lt ht)).1 =
      secondExponent (branchMonomial ε h r (t+1) ht).1
        (.inl 1) (.inl 2) (signedIndex 0 ε) (signedIndex 0 ε) := by
  ext a
  rcases a with a | a
  all_goals
    cases ε <;> by_cases ha : a = 0 <;> by_cases hb : a = 1 <;> by_cases hc : a = 2
    all_goals
      simp_all only [branchMonomial,branchExponent,secondExponent,signedIndex,
        Bool.false_eq_true,ite_false,ite_true,Finsupp.add_apply,Finsupp.tsub_apply,
        Finsupp.single_apply,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,
        eq_comm,ite_false,ite_true,zero_add,add_zero,Nat.sub_zero] <;> omega

lemma angularLie_branch_edges (ε : Bool) (h r t : ℕ) (ht : t < h) :
    single (branchMonomial ε h r (t+1) ht) (branchMonomial ε h r t (Nat.le_of_lt ht)) (1:ℂ)
      ∈ angularLie (2*h+r) ∧
    single (branchMonomial ε h r t (Nat.le_of_lt ht)) (branchMonomial ε h r (t+1) ht) (1:ℂ)
      ∈ angularLie (2*h+r) := by
  constructor
  · exact angularLie_legal_split 0 1 2 (by decide) (by decide) (by decide) ε true true
      _ _ (branchMonomial_extreme ε h r (t+1) ht) (branchMonomial_extreme ε h r t (Nat.le_of_lt ht))
      (branchMonomial_pair_count ε h r t ht) (branchMonomial_split ε h r t ht)
  · apply angularLie_legal_merge 0 1 2 (by decide) (by decide) (by decide) ε true true
      _ _ (branchMonomial_extreme ε h r t (Nat.le_of_lt ht)) (branchMonomial_extreme ε h r (t+1) ht)
    · rw [show signedIndex (1:Fin 8) true = .inl 1 by rfl,branchMonomial_coordinate]
      omega
    · change 1 ≤ (branchMonomial ε h r (t+1) ht).1 (.inl 2)
      cases ε <;> norm_num [branchMonomial,branchExponent,signedIndex,Finsupp.single_apply,Fin.ext_iff,Sum.inr_ne_inl]
    · exact branchMonomial_merge ε h r t ht

lemma angularLie_branch_endpoints (ε : Bool) (h r t : ℕ) (ht : t ≤ h) (hp : 0 < t) :
    single (branchMonomial ε h r t ht) (branchMonomial ε h r 0 (Nat.zero_le h)) (1:ℂ)
      ∈ angularLie (2*h+r) ∧
    single (branchMonomial ε h r 0 (Nat.zero_le h)) (branchMonomial ε h r t ht) (1:ℂ)
      ∈ angularLie (2*h+r) := by
  induction t with
  | zero => omega
  | succ t ih =>
    have he := angularLie_branch_edges ε h r t ht
    by_cases hz : t = 0
    · subst t; exact he
    · have hi := ih (by omega) (by omega)
      have hn := branchMonomial_distinct ε h r (t+1) 0 ht (Nat.zero_le h) (by omega)
      constructor
      · have hb := (angularLie (2*h+r)).lie_mem he.1 hi.1
        rw [bracket_units _ _ _ hn.symm] at hb
        exact hb
      · have hb := (angularLie (2*h+r)).lie_mem hi.2 he.2
        rw [bracket_units _ _ _ hn] at hb
        exact hb

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open Matrix MvPolynomial HarmonicCounterexample.Berger
open HarmonicCounterexample.Berger.ComplexStructure
attribute [local instance 100] LieRing.ofAssociativeRing

def pureMonomial (ε : Bool) (l : ℕ) : MonomialIndex (Fin 8 ⊕ Fin 8) l :=
  ⟨Finsupp.single (signedIndex 0 ε) l,Finsupp.degree_single _ _⟩

lemma pureMonomial_ne {l : ℕ} (hl : 0 < l) : pureMonomial false l ≠ pureMonomial true l := by
  intro h
  have he := congrArg (fun p : MonomialIndex (Fin 8 ⊕ Fin 8) l => p.1 (.inl 0)) h
  norm_num [pureMonomial,signedIndex,Finsupp.single_apply,Fin.ext_iff,Sum.inr_ne_inl] at he
  omega

lemma branchMonomial_start (ε : Bool) (h r : ℕ) :
    branchMonomial ε h r 0 (Nat.zero_le h) = pureMonomial ε (2*h+r) := by
  apply Subtype.ext
  simp [branchMonomial,branchExponent,pureMonomial]

lemma evenBranch_common (h : ℕ) :
    branchMonomial false h 0 h le_rfl = branchMonomial true h 0 h le_rfl := by
  apply Subtype.ext
  simp [branchMonomial,branchExponent]

lemma angularLie_even_endpoint (h : ℕ) (hh : 0 < h) :
    single (pureMonomial true (2*h)) (pureMonomial false (2*h)) (1:ℂ) ∈ angularLie (2*h) := by
  have hm := angularLie_branch_endpoints false h 0 h le_rfl hh
  have hp := angularLie_branch_endpoints true h 0 h le_rfl hh
  rw [evenBranch_common] at hm
  have hb := (angularLie (2*h+0)).lie_mem hp.2 hm.1
  rw [branchMonomial_start,branchMonomial_start] at hb
  rw [bracket_units _ _ _ (pureMonomial_ne (by omega))] at hb
  simpa only [Nat.add_zero] using hb

/-- Common vertex of the two odd branches, using the fourth coordinate plane. -/
def oddEndpoint (h : ℕ) (hh : 0 < h) : MonomialIndex (Fin 8 ⊕ Fin 8) (2*h+1) :=
  ⟨Finsupp.single (.inl 1) (h-1)+Finsupp.single (.inl 2) h+Finsupp.single (.inl 3) 2,by
    simp only [map_add,Finsupp.degree_single]
    omega⟩

lemma oddEndpoint_extreme (h : ℕ) (hh : 0 < h) : ExtremeMonomial (oddEndpoint h hh) := by
  intro a
  right
  simp [oddEndpoint]

lemma oddEndpoint_ne_pure (ε : Bool) (h : ℕ) (hh : 0 < h) :
    oddEndpoint h hh ≠ pureMonomial ε (2*h+1) := by
  intro he
  have ht := congrArg (fun p : MonomialIndex (Fin 8 ⊕ Fin 8) (2*h+1) => p.1 (.inl 2)) he
  cases ε <;> norm_num [oddEndpoint,pureMonomial,signedIndex,Finsupp.single_apply,Fin.ext_iff,Sum.inr_ne_inl] at ht
  all_goals omega

lemma oddEndpoint_merge (ε : Bool) (h : ℕ) (hh : 0 < h) :
    (oddEndpoint h hh).1 = secondExponent (branchMonomial ε h 1 h le_rfl).1
      (signedIndex 0 ε) (.inl 1) (.inl 3) (.inl 3) := by
  ext a
  rcases a with a | a
  all_goals
    cases ε <;> by_cases ha : a = 0 <;> by_cases hb : a = 1 <;>
      by_cases hc : a = 2 <;> by_cases hd : a = 3
    all_goals
      simp_all only [oddEndpoint,branchMonomial,branchExponent,secondExponent,signedIndex,
        Bool.false_eq_true,ite_false,ite_true,Finsupp.add_apply,Finsupp.tsub_apply,
        Finsupp.single_apply,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,
        eq_comm,ite_false,ite_true,zero_add,add_zero,Nat.sub_zero,Nat.sub_self,mul_zero] <;> omega

lemma oddEndpoint_split (ε : Bool) (h : ℕ) (hh : 0 < h) :
    (branchMonomial ε h 1 h le_rfl).1 = secondExponent (oddEndpoint h hh).1
      (.inl 3) (.inl 3) (signedIndex 0 ε) (.inl 1) := by
  ext a
  rcases a with a | a
  all_goals
    cases ε <;> by_cases ha : a = 0 <;> by_cases hb : a = 1 <;>
      by_cases hc : a = 2 <;> by_cases hd : a = 3
    all_goals
      simp_all only [oddEndpoint,branchMonomial,branchExponent,secondExponent,signedIndex,
        Bool.false_eq_true,ite_false,ite_true,Finsupp.add_apply,Finsupp.tsub_apply,
        Finsupp.single_apply,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,
        eq_comm,ite_false,ite_true,zero_add,add_zero,Nat.sub_zero,Nat.sub_self,mul_zero] <;> omega

lemma angularLie_odd_last_edges (ε : Bool) (h : ℕ) (hh : 0 < h) :
    single (oddEndpoint h hh) (branchMonomial ε h 1 h le_rfl) (1:ℂ) ∈ angularLie (2*h+1) ∧
    single (branchMonomial ε h 1 h le_rfl) (oddEndpoint h hh) (1:ℂ) ∈ angularLie (2*h+1) := by
  constructor
  · apply angularLie_legal_merge 3 0 1 (by decide) (by decide) (by decide) true ε true
      _ _ (oddEndpoint_extreme h hh) (branchMonomial_extreme ε h 1 h le_rfl)
    · cases ε <;> norm_num [branchMonomial,branchExponent,signedIndex,Finsupp.single_apply,Fin.ext_iff,Sum.inr_ne_inl]
    · rw [show signedIndex (1:Fin 8) true = .inl 1 by rfl,branchMonomial_coordinate]
      exact hh
    · exact oddEndpoint_merge ε h hh
  · apply angularLie_legal_split 3 0 1 (by decide) (by decide) (by decide) true ε true
      _ _ (branchMonomial_extreme ε h 1 h le_rfl) (oddEndpoint_extreme h hh)
    · norm_num [oddEndpoint,signedIndex,Finsupp.single_apply,Fin.ext_iff,Sum.inr_ne_inl]
    · exact oddEndpoint_split ε h hh

lemma angularLie_odd_branch_endpoints (ε : Bool) (h : ℕ) (hh : 0 < h) :
    single (oddEndpoint h hh) (pureMonomial ε (2*h+1)) (1:ℂ) ∈ angularLie (2*h+1) ∧
    single (pureMonomial ε (2*h+1)) (oddEndpoint h hh) (1:ℂ) ∈ angularLie (2*h+1) := by
  have hb := angularLie_branch_endpoints ε h 1 h le_rfl hh
  rw [branchMonomial_start] at hb
  have he := angularLie_odd_last_edges ε h hh
  constructor
  · have hc := (angularLie (2*h+1)).lie_mem he.1 hb.1
    rw [bracket_units _ _ _ (oddEndpoint_ne_pure ε h hh).symm] at hc
    exact hc
  · have hc := (angularLie (2*h+1)).lie_mem hb.2 he.2
    rw [bracket_units _ _ _ (oddEndpoint_ne_pure ε h hh)] at hc
    exact hc

lemma angularLie_odd_endpoint (h : ℕ) (hh : 0 < h) :
    single (pureMonomial true (2*h+1)) (pureMonomial false (2*h+1)) (1:ℂ) ∈ angularLie (2*h+1) := by
  have hm := angularLie_odd_branch_endpoints false h hh
  have hp := angularLie_odd_branch_endpoints true h hh
  have hb := (angularLie (2*h+1)).lie_mem hp.2 hm.1
  rw [bracket_units _ _ _ (pureMonomial_ne (by omega))] at hb
  exact hb

/-- A genuine rank-one endpoint unit on every degree needed in the n=16
construction. This is produced, not hypothesized. -/
theorem angularLie_endpoint (l : ℕ) (hl : 2 ≤ l) :
    single (pureMonomial true l) (pureMonomial false l) (1:ℂ) ∈ angularLie l := by
  rcases Nat.mod_two_eq_zero_or_one l with he | ho
  · have hl' : l = 2*(l/2) := by omega
    rw [hl']
    exact angularLie_even_endpoint (l/2) (by omega)
  · have hl' : l = 2*(l/2)+1 := by omega
    rw [hl']
    exact angularLie_odd_endpoint (l/2) (by omega)

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open MvPolynomial Matrix
open scoped BigOperators
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

/-- Actual substitution of a linear coordinate motion in a polynomial. -/
def linearChange (M : Matrix ι ι 𝕜) : MvPolynomial ι 𝕜 →ₐ[𝕜] MvPolynomial ι 𝕜 :=
  aeval (fun i => ∑ j : ι,M i j • X j)

omit [DecidableEq ι] in
lemma linearChange_X (M : Matrix ι ι 𝕜) (i : ι) :
    linearChange M (X i) = ∑ j : ι,M i j • X j := aeval_X _ _

lemma linearChange_one : linearChange (1 : Matrix ι ι 𝕜) = AlgHom.id 𝕜 _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [linearChange_X,Matrix.one_apply]

omit [DecidableEq ι] in
lemma linearChange_comp (M N : Matrix ι ι 𝕜) :
    (linearChange M).comp (linearChange N) = linearChange (N*M) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply,linearChange_X,map_sum,map_smul,Matrix.mul_apply,
    Finset.sum_smul,Finset.smul_sum,smul_smul]
  exact Finset.sum_comm

omit [DecidableEq ι] in
lemma linearChange_linearField_X (M N K : Matrix ι ι 𝕜) (h : N*M=M*K) (i : ι) :
    linearChange M (linearField N (X i)) = linearField K (linearChange M (X i)) := by
  simp only [linearField_X,linearChange_X,map_sum,map_smul,Derivation.map_smul,
    Finset.smul_sum,smul_smul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_smul,← Finset.sum_smul]
  exact congrArg (fun a : 𝕜 => a • (X k : MvPolynomial ι 𝕜))
    (congrArg (fun A : Matrix ι ι 𝕜 => A i k) h)

omit [DecidableEq ι] in
lemma linearChange_linearField (M N K : Matrix ι ι 𝕜) (h : N*M=M*K) (P : MvPolynomial ι 𝕜) :
    linearChange M (linearField N P) = linearField K (linearChange M P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [linearChange]
  | add P Q hp hq => simp only [map_add,hp,hq]
  | mul_X P i hp =>
    simp only [Derivation.leibniz,smul_eq_mul,map_add,map_mul,hp,linearChange_linearField_X M N K h]

omit [DecidableEq ι] in
lemma linearChange_homogeneous {l : ℕ} {P : MvPolynomial ι 𝕜}
    (hP : P.IsHomogeneous l) (M : Matrix ι ι 𝕜) : (linearChange M P).IsHomogeneous l := by
  have h := hP.aeval (fun i => ∑ j : ι,M i j • (X j : MvPolynomial ι 𝕜)) (n := 1) (by
    intro i
    apply IsHomogeneous.sum
    intro j _
    simpa only [smul_eq_C_mul] using (isHomogeneous_X 𝕜 j).C_mul (M i j))
  simpa only [linearChange,one_mul] using h

def homogeneousChange (l : ℕ) (M : Matrix ι ι 𝕜) :
    Module.End 𝕜 (homogeneousSubmodule ι 𝕜 l) where
  toFun P := ⟨linearChange M P.1,linearChange_homogeneous P.2 M⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

omit [DecidableEq ι] in
lemma homogeneousChange_apply_val (l : ℕ) (M : Matrix ι ι 𝕜)
    (P : homogeneousSubmodule ι 𝕜 l) :
    (homogeneousChange l M P).1 = linearChange M P.1 := rfl

lemma homogeneousChange_one (l : ℕ) : homogeneousChange l (1 : Matrix ι ι 𝕜) = 1 := by
  ext P : 1
  apply Subtype.ext
  change linearChange 1 P.1 = P.1
  rw [linearChange_one]
  rfl

omit [DecidableEq ι] in
lemma homogeneousChange_mul (l : ℕ) (M N : Matrix ι ι 𝕜) :
    homogeneousChange l M*homogeneousChange l N = homogeneousChange l (N*M) := by
  ext P : 1
  apply Subtype.ext
  exact AlgHom.congr_fun (linearChange_comp M N) P.1

lemma homogeneousChange_field (l : ℕ) (M N K : Matrix ι ι 𝕜) (h : N*M=M*K) :
    homogeneousChange l M*homogeneousField l N = homogeneousField l K*homogeneousChange l M := by
  ext P : 1
  apply Subtype.ext
  exact linearChange_linearField M N K h P.1

def homogeneousChangeMatrix (l : ℕ) (M : Matrix ι ι 𝕜) :
    Matrix (MonomialIndex ι l) (MonomialIndex ι l) 𝕜 :=
  LinearMap.toMatrixAlgEquiv (homogeneousBasis l) (homogeneousChange l M)

lemma homogeneousChangeMatrix_one (l : ℕ) : homogeneousChangeMatrix l (1 : Matrix ι ι 𝕜) = 1 := by
  unfold homogeneousChangeMatrix
  rw [homogeneousChange_one,map_one]

lemma homogeneousChangeMatrix_mul (l : ℕ) (M N : Matrix ι ι 𝕜) :
    homogeneousChangeMatrix l M*homogeneousChangeMatrix l N = homogeneousChangeMatrix l (N*M) := by
  unfold homogeneousChangeMatrix
  rw [← map_mul,homogeneousChange_mul]

lemma homogeneousChangeMatrix_field (l : ℕ) (M N K : Matrix ι ι 𝕜) (h : N*M=M*K) :
    homogeneousChangeMatrix l M*homogeneousMatrix l N = homogeneousMatrix l K*homogeneousChangeMatrix l M := by
  change (LinearMap.toMatrixAlgEquiv (homogeneousBasis l) (homogeneousChange l M))*
      (LinearMap.toMatrixAlgEquiv (homogeneousBasis l) (homogeneousField l N)) =
    (LinearMap.toMatrixAlgEquiv (homogeneousBasis l) (homogeneousField l K))*
      (LinearMap.toMatrixAlgEquiv (homogeneousBasis l) (homogeneousChange l M))
  rw [← map_mul,← map_mul,homogeneousChange_field l M N K h]

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Berger.ComplexStructure
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Orthogonal coordinate conjugation, including both orientation components. -/
def orthogonalConjugate (J : ComplexStructure ι) (R : Matrix ι ι ℝ)
    (hR : Rᵀ*R = 1) : ComplexStructure ι where
  matrix := Rᵀ*J.matrix*R
  square := by
    have hRR : R*Rᵀ = 1 := mul_eq_one_comm.1 hR
    calc
      (Rᵀ*J.matrix*R)*(Rᵀ*J.matrix*R) = Rᵀ*(J.matrix*J.matrix)*R := by
        simp only [mul_assoc,← mul_assoc R Rᵀ,hRR,one_mul]
      _ = -1 := by rw [J.square,mul_neg,mul_one,neg_mul,hR]
  orthogonal := by
    have hRR : R*Rᵀ = 1 := mul_eq_one_comm.1 hR
    simp only [transpose_mul,transpose_transpose,mul_assoc,
      ← mul_assoc R Rᵀ,hRR,one_mul,← mul_assoc J.matrixᵀ J.matrix,J.orthogonal]
    exact hR

lemma splitFieldMatrix_one (s : ℕ) : splitFieldMatrix (1 : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ) = 1 := by
  change splitChange s * _ * unsplitChange s = 1
  have h : (1 : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ).map Complex.ofReal = 1 := by
    exact Complex.ofRealHom.mapMatrix.map_one
  rw [h,mul_one,split_unsplit]

end HarmonicCounterexample.Berger.ComplexStructure

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open Matrix MvPolynomial HarmonicCounterexample.Berger
open HarmonicCounterexample.Berger.ComplexStructure
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

lemma matrix_conjugate_traceFree (G H A : Matrix ι ι 𝕜) (hGH : G*H = 1) (hHG : H*G = 1) :
    G*traceFree A*H = traceFree (G*A*H) := by
  have ht : (G*A*H).trace = A.trace := by
    rw [Matrix.trace_mul_cycle, hHG,one_mul]
  simp only [traceFree,LinearMap.coe_mk,AddHom.coe_mk,mul_sub,sub_mul,
    mul_smul_comm,smul_mul_assoc,mul_one,hGH,ht]

lemma matrix_conjugate_lie (G H A B : Matrix ι ι 𝕜) (hHG : H*G = 1) :
    G*⁅A,B⁆*H = ⁅G*A*H,G*B*H⁆ := by
  change G*(A*B-B*A)*H = (G*A*H)*(G*B*H)-(G*B*H)*(G*A*H)
  simp only [mul_sub,sub_mul,mul_assoc,← mul_assoc H G,hHG,one_mul]

/-- Conjugation closure follows from closure of the actual generators. -/
lemma conjugation_lieSpan (T : Set (Matrix ι ι 𝕜)) (G H : Matrix ι ι 𝕜) (hHG : H*G = 1)
    (hT : ∀ A ∈ T,G*A*H ∈ LieSubalgebra.lieSpan 𝕜 _ T) :
    ∀ A ∈ LieSubalgebra.lieSpan 𝕜 _ T,G*A*H ∈ LieSubalgebra.lieSpan 𝕜 _ T := by
  intro A hA
  induction hA using LieSubalgebra.lieSpan_induction with
  | mem A hA => exact hT A hA
  | zero => simpa only [mul_zero,zero_mul] using (LieSubalgebra.lieSpan 𝕜 _ T).zero_mem
  | add A B hA hB ihA ihB =>
    simpa only [mul_add,add_mul] using (LieSubalgebra.lieSpan 𝕜 _ T).add_mem ihA ihB
  | smul c A hA ih =>
    simpa only [mul_smul_comm,smul_mul_assoc] using (LieSubalgebra.lieSpan 𝕜 _ T).smul_mem c ih
  | lie A B hA hB ihA ihB =>
    rw [matrix_conjugate_lie G H A B hHG]
    exact (LieSubalgebra.lieSpan 𝕜 _ T).lie_mem ihA ihB

variable {s : ℕ}

def angularChange (l : ℕ) (R : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ) :=
  homogeneousChangeMatrix l (splitFieldMatrix R)

lemma angularChange_orthogonal (l : ℕ) (R : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ)
    (hR : Rᵀ*R = 1) : angularChange l R*angularChange l Rᵀ = 1 := by
  unfold angularChange
  rw [homogeneousChangeMatrix_mul,← splitFieldMatrix_mul,hR,splitFieldMatrix_one,homogeneousChangeMatrix_one]

lemma angularChange_field (l : ℕ) (R : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ)
    (hR : Rᵀ*R = 1) (J : ComplexStructure (Fin s ⊕ Fin s)) :
    angularChange l R*angularRepresentation l J.matrix*angularChange l Rᵀ =
      angularRepresentation l (J.orthogonalConjugate R hR).matrix := by
  have hRR : R*Rᵀ = 1 := mul_eq_one_comm.1 hR
  have hi : splitFieldMatrix J.matrix*splitFieldMatrix R =
      splitFieldMatrix R*splitFieldMatrix (J.orthogonalConjugate R hR).matrix := by
    rw [← splitFieldMatrix_mul,← splitFieldMatrix_mul]
    congr 1
    change J.matrix*R = R*(Rᵀ*J.matrix*R)
    simp only [← mul_assoc,hRR,one_mul]
  change homogeneousChangeMatrix l (splitFieldMatrix R)*homogeneousMatrix l (splitFieldMatrix J.matrix)*
    angularChange l Rᵀ = homogeneousMatrix l (splitFieldMatrix (J.orthogonalConjugate R hR).matrix)
  rw [homogeneousChangeMatrix_field l _ _ _ hi,mul_assoc]
  change _*(angularChange l R*angularChange l Rᵀ) = _
  rw [angularChange_orthogonal l R hR,mul_one]

lemma angularLie_orthogonal_conjugate (l : ℕ) (R : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ)
    (hR : Rᵀ*R = 1) : ∀ A ∈ angularLie l,
    angularChange l R*A*angularChange l Rᵀ ∈ angularLie l := by
  have hRR : R*Rᵀ = 1 := mul_eq_one_comm.1 hR
  have hG := angularChange_orthogonal l R hR
  have hH : angularChange l Rᵀ*angularChange l R = 1 := by
    simpa only [transpose_transpose] using angularChange_orthogonal l Rᵀ (by simpa using hRR)
  apply conjugation_lieSpan _ _ _ hH
  rintro _ ⟨J,rfl⟩
  rw [matrix_conjugate_traceFree _ _ _ hG hH]
  have he : angularChange l R*(angularRepresentation l J.matrix*angularRepresentation l J.matrix)*angularChange l Rᵀ =
      angularRepresentation l (J.orthogonalConjugate R hR).matrix*
      angularRepresentation l (J.orthogonalConjugate R hR).matrix := by
    rw [← angularChange_field l R hR J]
    simp only [mul_assoc,← mul_assoc (angularChange l Rᵀ) (angularChange l R),hH,one_mul]
  rw [he]
  exact angularLie_generator l (J.orthogonalConjugate R hR)

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Berger.ComplexStructure
open Matrix
variable {s : ℕ}

lemma splitFieldMatrix_apply (M : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ) (a b) :
    splitFieldMatrix M a b =
       (1/2:ℂ)*((M (.inl (coordinatePlane a)) (.inl (coordinatePlane b)):ℂ)
    -coordinateSign b*Complex.I*(M (.inl (coordinatePlane a)) (.inr (coordinatePlane b)):ℂ)
    +coordinateSign a*Complex.I*(M (.inr (coordinatePlane a)) (.inl (coordinatePlane b)):ℂ)
    +coordinateSign a*coordinateSign b*(M (.inr (coordinatePlane a)) (.inr (coordinatePlane b)):ℂ)) := by
  rcases a with a | a <;> rcases b with b | b
  all_goals
    change (splitChange s*M.map Complex.ofReal*unsplitChange s) _ _ = _
    simp [splitChange,unsplitChange,coordinatePlane,coordinateSign,
      Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply]
  all_goals ring_nf; simp only [Complex.I_sq]; ring

lemma splitFieldMatrix_skew (M : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ)
    (hM : Mᵀ = -M) (a b : Fin s ⊕ Fin s) :
    splitFieldMatrix M b (Sum.swap a) = -splitFieldMatrix M a (Sum.swap b) := by
  have h (i j : Fin s ⊕ Fin s) : (M j i:ℂ) = -(M i j:ℂ) := by
    exact_mod_cast congrArg (fun N : Matrix _ _ ℝ => N i j) hM
  rw [splitFieldMatrix_apply,splitFieldMatrix_apply]
  rcases a with a | a <;> rcases b with b | b
  all_goals
    simp only [Sum.swap_inl,Sum.swap_inr,coordinatePlane,coordinateSign,Sum.elim_inl,Sum.elim_inr,id_eq]
    rw [h (.inl a) (.inl b),h (.inr a) (.inl b),h (.inl a) (.inr b),h (.inr a) (.inr b)]
    ring

end HarmonicCounterexample.Berger.ComplexStructure

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extension of an actual ordered real orthonormal two-frame to an orthogonal
coordinate matrix. Both orientation classes are intentionally allowed. -/
lemma orthogonalMatrix_two_rows (i j : ι) (hij : i ≠ j)
    (u v : EuclideanSpace ℝ ι)
    (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 0) :
    ∃ R : Matrix ι ι ℝ,Rᵀ*R = 1 ∧ (∀ a,R i a = u a) ∧ (∀ a,R j a = v a) := by
  let f : ι → EuclideanSpace ℝ ι := fun a => if a=i then u else if a=j then v else 0
  have hf : Orthonormal ℝ (({i,j}:Set ι).domRestrict f) := by
    rw [orthonormal_iff_ite]
    intro a b
    have ha : a.1=i ∨ a.1=j := by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using a.2
    have hb : b.1=i ∨ b.1=j := by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using b.2
    rcases ha with ha | ha <;> rcases hb with hb | hb
    all_goals
      have ha' : (a=b) ↔ (a.1=b.1) := Subtype.ext_iff
      simp only [ha',Set.domRestrict_apply,f,ha,hb,ite_eq_right hij,ite_eq_right hij.symm]
      first | exact hu | exact hv | exact huv | exact (real_inner_comm u v).trans huv
  obtain ⟨b,hb⟩ := hf.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let R : Matrix ι ι ℝ := fun a c => b a c
  have hr : R*Rᵀ = 1 := by
    ext a c
    have he := (orthonormal_iff_ite.1 b.orthonormal) a c
    change (∑ x : ι,b a x*b c x) = if a=c then 1 else 0
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,mul_comm] using he
  refine ⟨R,mul_eq_one_comm.1 hr,?_,?_⟩
  · intro a
    have h := hb i (by simp)
    simp only [f,ite_true] at h
    exact congrArg (fun x : EuclideanSpace ℝ ι => x a) h
  · intro a
    have h := hb j (by simp)
    simp only [f,Ne.symm hij,ite_false,ite_true] at h
    exact congrArg (fun x : EuclideanSpace ℝ ι => x a) h

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma complex_null_parts (z : ι → ℂ) (hz : ∑ a : ι,z a*z a = 0) :
    (∑ a : ι,(z a).re*(z a).re) = ∑ a : ι,(z a).im*(z a).im ∧
    (∑ a : ι,(z a).re*(z a).im) = 0 := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp only [Complex.re_sum,Complex.mul_re,Complex.zero_re,Finset.sum_sub_distrib] at hr
  simp only [Complex.im_sum,Complex.mul_im,Complex.zero_im] at hi
  have he : (∑ a : ι,((z a).re*(z a).im+(z a).im*(z a).re)) =
      2*∑ a : ι,(z a).re*(z a).im := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he] at hi
  exact ⟨sub_eq_zero.1 hr,by linarith⟩

/-- Every nonzero complex-null vector really is a scalar multiple of an
orthogonal real two-frame; this is not an orbit-transitivity assumption. -/
lemma nullVector_orthogonal_frame (i j : ι) (hij : i ≠ j)
    (z : ι → ℂ) (hz : ∑ a : ι,z a*z a = 0) (hn : z ≠ 0) :
    ∃ (r : ℝ) (R : Matrix ι ι ℝ),0 < r ∧ Rᵀ*R = 1 ∧
      ∀ a,z a = (r:ℂ)*((R i a:ℂ)+Complex.I*(R j a:ℂ)) := by
  let u : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun a => (z a).re)
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun a => (z a).im)
  have hp := complex_null_parts z hz
  have heq : inner ℝ u u = inner ℝ v v := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,u,v,
      PiLp.toLp_apply] using hp.1
  have huv : inner ℝ u v = 0 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,u,v,
      PiLp.toLp_apply,mul_comm] using hp.2
  have hu : u ≠ 0 := by
    intro h
    have hv : v = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).1
      rw [← heq,h,inner_zero_left]
    apply hn
    funext a
    apply Complex.ext
    · have hh := congrArg (fun x : EuclideanSpace ℝ ι => x a) h
      exact hh
    · have hh := congrArg (fun x : EuclideanSpace ℝ ι => x a) hv
      exact hh
  let r := ‖u‖
  have hr : 0 < r := norm_pos_iff.2 hu
  have hr0 : r ≠ 0 := ne_of_gt hr
  have huu : inner ℝ u u = r^2 := real_inner_self_eq_norm_sq u
  have hvv : inner ℝ v v = r^2 := heq.symm.trans huu
  have hun : inner ℝ (r⁻¹ • u) (r⁻¹ • u) = 1 := by
    simp only [real_inner_smul_left,inner_smul_right,huu]
    field_simp
  have hvn : inner ℝ (r⁻¹ • v) (r⁻¹ • v) = 1 := by
    simp only [real_inner_smul_left,inner_smul_right,hvv]
    field_simp
  have huv' : inner ℝ (r⁻¹ • u) (r⁻¹ • v) = 0 := by
    simp only [real_inner_smul_left,inner_smul_right,huv,mul_zero]
  obtain ⟨R,hR,hRi,hRj⟩ := orthogonalMatrix_two_rows i j hij (r⁻¹ • u) (r⁻¹ • v) hun hvn huv'
  refine ⟨r,R,hr,hR,?_⟩
  intro a
  rw [hRi a,hRj a]
  change z a = (r:ℂ)*(((r⁻¹*(z a).re:ℝ):ℂ)+Complex.I*((r⁻¹*(z a).im:ℝ):ℂ))
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,hr0,← mul_assoc]

end HarmonicCounterexample.Control

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Berger.ComplexStructure
open Matrix
variable {s : ℕ}

lemma splitFieldMatrix_transpose (R : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ)
    (a b : Fin s ⊕ Fin s) :
    splitFieldMatrix Rᵀ (Sum.swap b) (Sum.swap a) = splitFieldMatrix R a b := by
  rw [splitFieldMatrix_apply,splitFieldMatrix_apply]
  rcases a with a | a <;> rcases b with b | b
  all_goals
    simp only [Sum.swap_inl,Sum.swap_inr,coordinatePlane,coordinateSign,
      Sum.elim_inl,Sum.elim_inr,id_eq,Matrix.transpose_apply]
    ring

end HarmonicCounterexample.Berger.ComplexStructure

end

noncomputable section
open Matrix
open scoped BigOperators
open scoped Topology
open Filter
open Matrix
open scoped BigOperators
open Matrix MvPolynomial
open Matrix

namespace HarmonicCounterexample.Control
open Matrix HarmonicCounterexample.Berger.ComplexStructure
open scoped BigOperators
variable {s : ℕ}

/-- The null cone in complex split coordinates is the actual real orthogonal
orbit of the first isotropic coordinate, up to a nonzero real scale. -/
lemma split_null_row_orbit (i : Fin s) (a : (Fin s ⊕ Fin s) → ℂ)
    (ha : ∑ j : Fin s,a (.inl j)*a (.inr j) = 0) (hn : a ≠ 0) :
    ∃ (r : ℝ) (R : Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) ℝ),
      0 < r ∧ Rᵀ*R = 1 ∧ ∀ b,a b = (r:ℂ)*splitFieldMatrix R (.inl i) b := by
  let z : (Fin s ⊕ Fin s) → ℂ := Sum.elim
    (fun j => a (.inl j)+a (.inr j))
    (fun j => Complex.I*(a (.inl j)-a (.inr j)))
  have hz : ∑ b : Fin s ⊕ Fin s,z b*z b = 0 := by
    rw [Fintype.sum_sum_type,← Finset.sum_add_distrib]
    have he : ∀ j : Fin s,z (.inl j)*z (.inl j)+z (.inr j)*z (.inr j) =
        4*(a (.inl j)*a (.inr j)) := by
      intro j
      dsimp [z]
      ring_nf
      rw [Complex.I_sq]
      ring
    simp only [he,← Finset.mul_sum,ha,mul_zero]
  have hzn : z ≠ 0 := by
    intro h
    apply hn
    funext b
    rcases b with j | j
    all_goals
      have h1 := congrFun h (.inl j)
      have h2 := congrFun h (.inr j)
      change a (.inl j)+a (.inr j)=0 at h1
      change Complex.I*(a (.inl j)-a (.inr j))=0 at h2
      have h3 := (mul_eq_zero.1 h2).resolve_left Complex.I_ne_zero
    · change a (.inl j) = 0
      linear_combination (h1+h3)/2
    · change a (.inr j) = 0
      linear_combination (h1-h3)/2
  obtain ⟨r,R,hr,hR,hzR⟩ := nullVector_orthogonal_frame (.inl i) (.inr i) (by simp) z hz hzn
  refine ⟨r,R,hr,hR,?_⟩
  rintro (j | j)
  all_goals
    have hx := hzR (.inl j)
    have hy := hzR (.inr j)
    dsimp [z] at hx hy
    rw [splitFieldMatrix_apply]
    simp only [coordinatePlane,coordinateSign,Sum.elim_inl,Sum.elim_inr,id_eq]
  · linear_combination (norm := (ring_nf; rw [Complex.I_sq]; ring)) (hx-Complex.I*hy)/2
  · linear_combination (norm := (ring_nf; rw [Complex.I_sq]; ring)) (hx+Complex.I*hy)/2

end HarmonicCounterexample.Control

end

end OAI
