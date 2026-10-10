import OAI.Algebra.Determinantal.HalfPolynomials

namespace OAI
namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
universe u
variable {K L R : Type u} [Field K] [Field L] [Algebra K L]
  [CommRing R] [Algebra L R]

theorem add_evaluated_polynomial {ι : Type*} [Fintype ι]
    (F : IntermediateField K L) (n B : ℕ) (hF : Algebra.trdeg K F ≤ (n : Cardinal))
    (q : MvPolynomial (Fin 2) L →ₐ[L] R) (c : Basis ι L R)
    (hmon : ∀ s i, c.repr (q (monomial s (1 : L))) i ∈ F)
    (p t : MvPolynomial (Fin 2) L) (ht : InField F t)
    (hhigh : ∀ s, B ≤ s.degree → p.coeff s = t.coeff s)
    (hpq : ∀ i, c.repr (q p) i ∈ F) :
    ∃ E : IntermediateField K L, F ≤ E ∧ InField E p ∧
      Algebra.trdeg K E ≤ (n + (Fintype.card (Index B) - finrank L (filtered q B)) : ℕ) := by
  classical
  have he := remainder_expansion p t hhigh
  have hsum : ∑ s : Index B, (p-t).coeff s.val • q (monomial s.val 1) = q p-q t := by
    have hh := congrArg q he
    rw [map_add,map_sum] at hh
    simp only [map_smul] at hh
    exact eq_sub_of_add_eq (by simpa only [add_comm] using hh.symm)
  obtain ⟨E,hFE,hxE,hE⟩ := LinearParameters.add_constrained_parameters F n hF c
    (fun s : Index B => q (monomial s.val 1)) (fun s => (p-t).coeff s.val)
    (fun s i => hmon s.val i) (by
      intro i
      rw [hsum,map_sub]
      exact F.sub_mem (hpq i) (repr_polynomial_mem F q c hmon t ht i))
  refine ⟨E,hFE,?_,?_⟩
  · intro s
    by_cases hs : s.degree < B
    · have hh := hxE ⟨s,hs⟩
      rw [coeff_sub] at hh
      simpa only [sub_add_cancel] using E.add_mem hh (hFE (ht s))
    · rw [hhigh s (by omega)]
      exact hFE (ht s)
  · rwa [span_low] at hE

lemma evaluated_mem (F : IntermediateField K L) {p : MvPolynomial (Fin 2) L}
    (hp : InField F p) {x : Fin 2 → L} (hx : ∀ i, x i ∈ F) : eval x p ∈ F :=
  eval_mem (fun s _ => hp s) hx

lemma add_algebraic_closure (F : IntermediateField K L) (n : ℕ)
    (hF : Algebra.trdeg K F ≤ (n : Cardinal)) :
    let E := (algebraicClosure F L).restrictScalars K
    F ≤ E ∧ Algebra.trdeg K E ≤ (n : Cardinal) := by
  let E := algebraicClosure F L
  let : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).mpr
    (algebraMap F E).injective
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨fun x hx => E.algebraMap_mem ⟨x,hx⟩,?_⟩
  change Algebra.trdeg K E ≤ _
  rw [← trdeg_add_eq K F,trdeg_eq_zero (R := F),add_zero]
  exact hF

lemma node_values_mem [CharP L 2] (F : IntermediateField K L)
    (a b c d : MvPolynomial (Fin 2) L) (hbF : InField F b) (hcF : InField F c)
    (hdF : InField F d) (x : Fin 2 → L) (hd : eval x d ≠ 0)
    (hb : (eval x b)^2+x 1*(eval x d)^2=0)
    (hc : (eval x c)^2+x 0*(eval x d)^2=0)
    (ha : (eval x a)^2+x 0*(eval x b)^2+x 1*(eval x c)^2+x 0*x 1*(eval x d)^2=0) :
    (∀ i, x i ∈ algebraicClosure F L) ∧ eval x a ∈ algebraicClosure F L := by
  obtain ⟨b₀,hb₀⟩ := inField_lift F hbF
  obtain ⟨c₀,hc₀⟩ := inField_lift F hcF
  obtain ⟨d₀,hd₀⟩ := inField_lift F hdF
  have he (p : MvPolynomial (Fin 2) F) : aeval x p = eval x (p.map F.val.toRingHom) := by
    rw [eval_map]
    rfl
  have hx := FrobeniusPlane.node_coordinates_algebraic x b₀ c₀ d₀
    (by simpa only [he,hd₀] using hd) (by simpa only [he,hb₀,hd₀] using hb)
    (by simpa only [he,hc₀,hd₀] using hc)
  have hx' : ∀ i, x i ∈ algebraicClosure F L := fun i => mem_algebraicClosure_iff.mpr (hx i)
  refine ⟨hx',mem_algebraicClosure_iff.mpr ?_⟩
  apply IsAlgebraic.of_pow (n := 2) (by omega)
  apply mem_algebraicClosure_iff.mp
  have hFE : F ≤ (algebraicClosure F L).restrictScalars K := fun z hz =>
    (algebraicClosure F L).algebraMap_mem ⟨z,hz⟩
  have hb' := evaluated_mem ((algebraicClosure F L).restrictScalars K) (inField_mono hFE hbF) hx'
  have hc' := evaluated_mem ((algebraicClosure F L).restrictScalars K) (inField_mono hFE hcF) hx'
  have hd' := evaluated_mem ((algebraicClosure F L).restrictScalars K) (inField_mono hFE hdF) hx'
  have heq : (eval x a)^2 = -(x 0*(eval x b)^2+x 1*(eval x c)^2+x 0*x 1*(eval x d)^2) := by
    linear_combination ha
  rw [heq]
  exact neg_mem (add_mem (add_mem (mul_mem (hx' 0) (pow_mem hb' 2))
    (mul_mem (hx' 1) (pow_mem hc' 2))) (mul_mem (mul_mem (hx' 0) (hx' 1)) (pow_mem hd' 2)))

end PermanentBorder.CurveFamily

namespace PermanentBorder.CurveFamily
open MvPolynomial Module LowPlane PlaneHilbert
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

theorem adjoin_polynomial_family {κ : Type*} [Fintype κ]
    (F : IntermediateField K L) (n : ℕ) (hF : Algebra.trdeg K F ≤ (n : Cardinal))
    (B : κ → ℕ) (p : κ → MvPolynomial (Fin 2) L) (t : κ → MvPolynomial (Fin 2) K)
    (hhigh : ∀ i s, B i ≤ s.degree → (p i).coeff s=algebraMap K L ((t i).coeff s))
    (U : Finset κ) :
    ∃ E : IntermediateField K L, F ≤ E ∧ (∀ i ∈ U, InField E (p i)) ∧
      Algebra.trdeg K E ≤ (n+∑ i ∈ U, Fintype.card (Index (B i)) : ℕ) := by
  classical
  induction U using Finset.induction_on with
  | empty => exact ⟨F,le_rfl,by simp,by simpa using hF⟩
  | @insert i U hi ih =>
    obtain ⟨D,hFD,hpD,hD⟩ := ih
    obtain ⟨E,hDE,hpE,hE⟩ := adjoin_polynomial D _ (B i) hD (p i) (by
      intro s hs; rw [hhigh i s hs]; exact D.algebraMap_mem ((t i).coeff s))
    refine ⟨E,hFD.trans hDE,?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact hpE
      · exact inField_mono hDE (hpD j hj)
    · simpa only [Finset.sum_insert hi,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hE

noncomputable def pointEvaluation {ι : Type*} (x : ι → Fin 2 → L) :
    MvPolynomial (Fin 2) L →ₐ[L] (ι → L) := AlgHom.pi (fun i => aeval (x i))

lemma pointEvaluation_apply {ι : Type*} (x : ι → Fin 2 → L)
    (p : MvPolynomial (Fin 2) L) (i : ι) : pointEvaluation x p i = eval (x i) p := by
  simp [pointEvaluation,aeval_def]

theorem node_parameter_bound [CharP L 2] {ι : Type u} [Fintype ι]
    (x : ι → Fin 2 → L) (a b c d : MvPolynomial (Fin 2) L)
    (B₀ : ℕ) (B : Fin 3 → ℕ) (t₀ : MvPolynomial (Fin 2) K)
    (t : Fin 3 → MvPolynomial (Fin 2) K)
    (h₀ : ∀ s, B₀ ≤ s.degree → a.coeff s=algebraMap K L (t₀.coeff s))
    (h : ∀ i s, B i ≤ s.degree → (![b,c,d] i).coeff s=algebraMap K L ((t i).coeff s))
    (hd : ∀ i, eval (x i) d ≠ 0)
    (hb : ∀ i, (eval (x i) b)^2+x i 1*(eval (x i) d)^2=0)
    (hc : ∀ i, (eval (x i) c)^2+x i 0*(eval (x i) d)^2=0)
    (ha : ∀ i, (eval (x i) a)^2+x i 0*(eval (x i) b)^2+
      x i 1*(eval (x i) c)^2+x i 0*x i 1*(eval (x i) d)^2=0) :
    ∃ (E : IntermediateField K L) (n : ℕ), InField E a ∧ InField E b ∧ InField E c ∧
      InField E d ∧ Algebra.trdeg K E ≤ (n : Cardinal) ∧
      n+finrank L (filtered (pointEvaluation x) B₀) ≤
        Fintype.card (Index B₀)+∑ i, Fintype.card (Index (B i)) := by
  classical
  have hbot : Algebra.trdeg K (⊥ : IntermediateField K L) ≤ (0 : Cardinal) := by rw [trdeg_eq_zero]
  obtain ⟨F,_,hpF,hF⟩ := adjoin_polynomial_family (⊥ : IntermediateField K L) 0 hbot
    B ![b,c,d] t h Finset.univ
  simp only [Finset.mem_univ,forall_const,zero_add] at hpF hF
  let D := (algebraicClosure F L).restrictScalars K
  obtain ⟨hFD,hD⟩ := add_algebraic_closure F _ hF
  have hn := fun i => node_values_mem F a b c d (hpF 0) (hpF 1) (hpF 2)
    (x i) (hd i) (hb i) (hc i) (ha i)
  obtain ⟨E,hDE,hpE,hE⟩ := add_evaluated_polynomial D _ B₀ hD (pointEvaluation x)
    (Pi.basisFun L ι) (by
      intro s i
      rw [Pi.basisFun_repr,pointEvaluation_apply]
      apply evaluated_mem D _ (hn i).1
      intro j
      rw [coeff_monomial]
      split_ifs <;> simp)
    a (t₀.map (algebraMap K L)) (inField_map D _) (by
      intro s hs; rw [coeff_map]; exact h₀ s hs)
    (by intro i; rw [Pi.basisFun_repr,pointEvaluation_apply]; exact (hn i).2)
  refine ⟨E,_,hpE,inField_mono (hFD.trans hDE) (hpF 0),
    inField_mono (hFD.trans hDE) (hpF 1),inField_mono (hFD.trans hDE) (hpF 2),hE,?_⟩
  have hr := filtered_rank_le (pointEvaluation x) B₀
  omega

end PermanentBorder.CurveFamily

namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

abbrev Plane (K : Type*) [CommSemiring K] := MvPolynomial (Fin 2) K

noncomputable def squareForm (a b c d : Plane K) : Plane K :=
  a^2 + X 0*b^2 + X 1*c^2 + X 0*X 1*d^2

lemma squareForm_add (a b c d a' b' c' d' : Plane K) :
    squareForm (a+a') (b+b') (c+c') (d+d') =
      squareForm a b c d + squareForm a' b' c' d' := by
  have htwo : (2 : Plane K) = 0 := CharP.cast_eq_zero _ 2
  simp only [squareForm, add_sq, htwo, zero_mul, add_zero]
  ring

omit [CharP K 2] in
lemma squareForm_mul_zero (a b c d : Plane K) :
    squareForm a b c d * X 0 = squareForm (X 0*b) a (X 0*d) c := by
  unfold squareForm
  ring

omit [CharP K 2] in
lemma squareForm_mul_one (a b c d : Plane K) :
    squareForm a b c d * X 1 = squareForm (X 1*c) (X 1*d) a b := by
  unfold squareForm
  ring

theorem exists_squareForm [PerfectRing K 2] (f : Plane K) :
    ∃ a b c d : Plane K, f = squareForm a b c d := by
  induction f using MvPolynomial.induction_on with
  | C a =>
      refine ⟨C ((frobeniusEquiv K 2).symm a),0,0,0,?_⟩
      simp only [squareForm, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero]
      rw [← map_pow, frobeniusEquiv_symm_pow_p]
  | add f g hf hg =>
      obtain ⟨a,b,c,d,rfl⟩ := hf
      obtain ⟨a',b',c',d',rfl⟩ := hg
      exact ⟨a+a',b+b',c+c',d+d',(squareForm_add ..).symm⟩
  | mul_X f i hf =>
      obtain ⟨a,b,c,d,rfl⟩ := hf
      fin_cases i
      · exact ⟨X 0*b,a,X 0*d,c,squareForm_mul_zero ..⟩
      · exact ⟨X 1*c,X 1*d,a,b,squareForm_mul_one ..⟩

lemma pderiv_square (i : Fin 2) (a : Plane K) : pderiv i (a^2) = 0 := by
  have htwo : (2 : Plane K) = 0 := CharP.cast_eq_zero _ 2
  simp [htwo]

lemma squareForm_partial_zero (a b c d : Plane K) :
    pderiv 0 (squareForm a b c d) = b^2 + X 1*d^2 := by
  have htwo : (2 : Plane K) = 0 := CharP.cast_eq_zero _ 2
  simp [squareForm, htwo, mul_comm]

lemma squareForm_partial_one (a b c d : Plane K) :
    pderiv 1 (squareForm a b c d) = c^2 + X 0*d^2 := by
  have htwo : (2 : Plane K) = 0 := CharP.cast_eq_zero _ 2
  simp [squareForm, htwo, mul_comm]

lemma squareForm_mixed (a b c d : Plane K) :
    pderiv 1 (pderiv 0 (squareForm a b c d)) = d^2 := by
  rw [squareForm_partial_zero]
  have htwo : (2 : Plane K) = 0 := CharP.cast_eq_zero _ 2
  simp [htwo]

theorem wild_zero_iff (a b c d : Plane K) (p : Fin 2 → K) :
    (eval p (squareForm a b c d) = 0 ∧
      eval p (pderiv 0 (squareForm a b c d)) = 0 ∧
      eval p (pderiv 1 (squareForm a b c d)) = 0 ∧
      eval p (pderiv 1 (pderiv 0 (squareForm a b c d))) = 0) ↔
    eval p a = 0 ∧ eval p b = 0 ∧ eval p c = 0 ∧ eval p d = 0 := by
  rw [squareForm_mixed, squareForm_partial_zero, squareForm_partial_one]
  simp only [map_add, map_mul, map_pow, eval_X]
  constructor
  · rintro ⟨hf,hb,hc,hd⟩
    have hd' : eval p d = 0 := (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp hd
    simp only [hd', zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] at hb hc
    have hb' : eval p b = 0 := (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp hb
    have hc' : eval p c = 0 := (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp hc
    have ha' : eval p a = 0 := by
      apply (pow_eq_zero_iff (by omega : 2 ≠ 0)).mp
      simpa [squareForm,hb',hc',hd'] using hf
    exact ⟨ha',hb',hc',hd'⟩
  · rintro ⟨ha,hb,hc,hd⟩
    simp [squareForm,ha,hb,hc,hd]

end PermanentBorder.FrobeniusPlane

namespace PermanentBorder.FrobeniusPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharP K 2]

lemma squareForm_eq_zero_iff (a b c d : Plane K) :
    squareForm a b c d = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro hf
    have hd : d = 0 := by
      have hh := congrArg (fun f : Plane K => pderiv 1 (pderiv 0 f)) hf
      rw [squareForm_mixed] at hh
      simpa using hh
    have hb : b = 0 := by
      have hh := congrArg (pderiv (0 : Fin 2)) hf
      rw [squareForm_partial_zero, hd] at hh
      simpa using hh
    have hc : c = 0 := by
      have hh := congrArg (pderiv (1 : Fin 2)) hf
      rw [squareForm_partial_one, hd] at hh
      simpa using hh
    have ha : a = 0 := by simpa [squareForm, hb, hc, hd] using hf
    exact ⟨ha,hb,hc,hd⟩
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    simp [squareForm]

lemma squareForm_injective {a b c d a' b' c' d' : Plane K}
    (h : squareForm a b c d = squareForm a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hz : squareForm (a+a') (b+b') (c+c') (d+d') = 0 := by
    rw [squareForm_add,h]
    simpa using (CharTwo.add_self_eq_zero (squareForm a' b' c' d'))
  rcases (squareForm_eq_zero_iff ..).mp hz with ⟨ha,hb,hc,hd⟩
  exact ⟨CharTwo.add_eq_zero.mp ha, CharTwo.add_eq_zero.mp hb,
    CharTwo.add_eq_zero.mp hc, CharTwo.add_eq_zero.mp hd⟩

lemma wild_ideal_eq (a b c d : Plane K) :
    Ideal.span {squareForm a b c d,
      pderiv 0 (squareForm a b c d),
      pderiv 1 (squareForm a b c d),
      pderiv 1 (pderiv 0 (squareForm a b c d))} =
    Ideal.span {a^2,b^2,c^2,d^2} := by
  rw [squareForm_mixed, squareForm_partial_zero, squareForm_partial_one]
  let J : Ideal (Plane K) := Ideal.span {a^2,b^2,c^2,d^2}
  let W : Ideal (Plane K) := Ideal.span
    {squareForm a b c d,b^2+X 1*d^2,c^2+X 0*d^2,d^2}
  change W = J
  have ha : a^2 ∈ J := Ideal.subset_span (by simp)
  have hb : b^2 ∈ J := Ideal.subset_span (by simp)
  have hc : c^2 ∈ J := Ideal.subset_span (by simp)
  have hd : d^2 ∈ J := Ideal.subset_span (by simp)
  have hwd : d^2 ∈ W := Ideal.subset_span (by simp)
  have hwb : b^2 ∈ W := by
    have hh : b^2+X 1*d^2 ∈ W := Ideal.subset_span (by simp)
    exact (W.add_mem_iff_left (W.mul_mem_left _ hwd)).mp hh
  have hwc : c^2 ∈ W := by
    have hh : c^2+X 0*d^2 ∈ W := Ideal.subset_span (by simp)
    exact (W.add_mem_iff_left (W.mul_mem_left _ hwd)).mp hh
  have hwa : a^2 ∈ W := by
    have hh : squareForm a b c d ∈ W := Ideal.subset_span (by simp)
    dsimp only [squareForm] at hh
    exact (W.add_mem_iff_left (W.mul_mem_left _ hwb)).mp
      ((W.add_mem_iff_left (W.mul_mem_left _ hwc)).mp
        ((W.add_mem_iff_left (W.mul_mem_left _ hwd)).mp hh))
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact J.add_mem (J.add_mem (J.add_mem ha (J.mul_mem_left _ hb))
        (J.mul_mem_left _ hc)) (J.mul_mem_left _ hd)
    · exact J.add_mem hb (J.mul_mem_left _ hd)
    · exact J.add_mem hc (J.mul_mem_left _ hd)
    · exact hd
  · apply Ideal.span_le.mpr
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl|rfl|rfl|rfl
    · exact hwa
    · exact hwb
    · exact hwc
    · exact hwd

omit [CharP K 2] in
lemma squareForm_mul (r a b c d : Plane K) :
    squareForm (r*a) (r*b) (r*c) (r*d) = r^2 * squareForm a b c d := by
  unfold squareForm
  ring

theorem existsUnique_squareForm [PerfectRing K 2] (f : Plane K) :
    ∃! v : Fin 4 → Plane K, f = squareForm (v 0) (v 1) (v 2) (v 3) := by
  obtain ⟨a,b,c,d,h⟩ := exists_squareForm f
  refine ⟨![a,b,c,d],h,?_⟩
  intro v hv
  have hh := squareForm_injective (hv.symm.trans h)
  funext i
  fin_cases i
  · exact hh.1
  · exact hh.2.1
  · exact hh.2.2.1
  · exact hh.2.2.2

end PermanentBorder.FrobeniusPlane

end OAI
