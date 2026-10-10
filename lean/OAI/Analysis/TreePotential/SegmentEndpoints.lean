import OAI.Analysis.TreePotential.SegmentMixtures

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.Segments

section
variable {I : Type*} [Fintype I]

lemma norm_weighted_signed_sum {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (p σ : I → ℝ) (Z : I → V) (hp : ∀ i, 0 ≤ p i) (hσ : ∀ i, |σ i| ≤ 1) :
    ‖∑ i, (p i*σ i) • Z i‖ ≤ ∑ i, p i*‖Z i‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hp i)]
  exact mul_le_mul_of_nonneg_right (by nlinarith [hσ i,hp i] : p i*|σ i| ≤ p i) (norm_nonneg _)

lemma mixture_replacement_error {E : Finset Node} (hE : Initial (E : Set Node))
    {g : Node → ℝ} (hg : IsUnitTest g) (A : I → Atom) (p σ : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1) (hσ : ∀ i, |σ i| ≤ 1) :
    ‖(∑ i, (p i*σ i) • (A i).replacement g E)-
      completedTail unitTests E (∑ i, (p i*σ i) • (A i).inCore)‖ ≤
      Real.sqrt (2*(∑ i, p i*(1-(A i).pairing g))) := by
  have he : (∑ i, (p i*σ i) • (A i).replacement g E)-
      completedTail unitTests E (∑ i, (p i*σ i) • (A i).inCore) =
      ∑ i, (p i*σ i) • ((A i).replacement g E-completedTail unitTests E (A i).inCore) := by
    simp only [map_sum,map_smul,smul_sub,Finset.sum_sub_distrib]
  rw [he]
  apply (norm_weighted_signed_sum p σ _ hp hσ).trans
  apply (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ((A i).replacement_error hg E hE) (hp i))).trans
  have hh := weighted_sqrt_bound p hp hp1 (fun i => 2*(1-(A i).pairing g))
    (fun i => mul_nonneg (by norm_num) ((A i).defect hg).1)
  have he2 : (∑ i, p i*(2*(1-(A i).pairing g))) =
      2*(∑ i, p i*(1-(A i).pairing g)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simpa only [he2] using hh

lemma unsigned_energy_bound_on (Q : Finset Node) (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1) (r : I → Node → ℝ) (d : I → ℝ)
    (hc : ∀ i j, (∑ q ∈ Q, oppositeProduct (r i q) (r j q)) ≤ d i+d j) :
    (∑ q ∈ Q, (∑ i, p i*|r i q|)^2) ≤
      (∑ q ∈ Q, (∑ i, p i*r i q)^2)+4*(∑ i, p i*d i) := by
  have hc' : ∀ i j, (∑ q : Q, oppositeProduct (r i q.val) (r j q.val)) ≤ d i+d j := by
    intro i j
    exact (Finset.sum_coe_sort Q (fun q => oppositeProduct (r i q) (r j q))).trans_le (hc i j)
  have hh := unsigned_energy_bound p hp hp1 (fun i (q : Q) => r i q.val) d hc'
  exact (Finset.sum_coe_sort Q (fun q => (∑ i, p i*|r i q|)^2)).symm.trans_le
    (hh.trans_eq (congrArg (fun v : ℝ => v+4*(∑ i,p i*d i))
      (Finset.sum_coe_sort Q (fun q => (∑ i,p i*r i q)^2))))

lemma mixture_replacement_norm [Nonempty I]
    {E : Finset Node} (hE : Initial (E : Set Node)) {g : Node → ℝ}
    (hg : IsUnitTest g) (hsupp : ∀ v ∉ E, g v=0) (A : I → Atom) (p σ : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1) (hσ : ∀ i, |σ i| ≤ 1) :
    ‖∑ i, (p i*σ i) • (A i).replacement g E‖ ≤
      Real.sqrt (‖∑ i, p i • (A i).replacement g E‖^2 +
        4*(∑ i, p i*(1-(A i).pairing g))) := by
  let Q : Finset Node := (Finset.univ.biUnion (fun i => (A i).family.biUnion Segment.nodes)).filter (IsExit (E : Set Node))
  have hQ (q : Node) (hq : q ∈ Q) : IsExit (E : Set Node) q := (Finset.mem_filter.mp hq).2
  have hc (i : I) (S : Segment) (hS : S ∈ (A i).family) (q : Node) (hq : q ∈ S.nodes)
      (hex : IsExit (E : Set Node) q) : q ∈ Q := by
    refine Finset.mem_filter.mpr ⟨?_,hex⟩
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨S,hS,hq⟩⟩
  have hr (i : I) := (A i).replacement_exits hE hsupp Q hQ (hc i)
  have hb := norm_exit_mixture Q hQ (fun i q => (A i).terminal q)
    (fun i q => (A i).terminal_start q) p σ (fun i q => (A i).exitCoeff g q) hp hσ
  have hmass := signed_exit_mass_sq Q hQ (fun i q => (A i).terminal q)
    (fun i q => (A i).terminal_start q) p (fun i q => (A i).exitCoeff g q)
  have hen := unsigned_energy_bound_on Q p hp hp1 (fun i q => (A i).exitCoeff g q)
    (fun i => 1-(A i).pairing g) (fun i j => (A i).cancellation hE hg hsupp (A j) Q hQ)
  simp_rw [← hr] at hb hmass
  apply hb.trans
  apply Real.sqrt_le_sqrt
  linarith

lemma finite_mixture_tail_scalar {e d : ℝ} (he : 0 ≤ e) (hd : 0 ≤ d) :
    e+Real.sqrt (2*d)+Real.sqrt ((e+Real.sqrt (2*d))^2+4*d) ≤
      2*e+(Real.sqrt 2+Real.sqrt 6)*Real.sqrt d := by
  have hs2 := Real.sq_sqrt (show 0 ≤ 2*d by positivity)
  have hs6 := Real.sq_sqrt (show 0 ≤ 6*d by positivity)
  have h26 : Real.sqrt (2*d) ≤ Real.sqrt (6*d) := Real.sqrt_le_sqrt (by linarith)
  have hroot : Real.sqrt ((e+Real.sqrt (2*d))^2+4*d) ≤ e+Real.sqrt (6*d) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [mul_nonneg he (sub_nonneg.mpr h26)]
  have heq : Real.sqrt (2*d)+Real.sqrt (6*d)=(Real.sqrt 2+Real.sqrt 6)*Real.sqrt d := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 6)]
    ring
  linarith

/-- The finite-state endpoint argument: replacement, actual exit cancellation,
unsigned mass, and both approximation errors appear explicitly. -/
theorem finite_mixture_tail [Nonempty I]
    {E : Finset Node} (hE : Initial (E : Set Node)) (x y : DualCore)
    (hx : completedHead unitTests E x=x) (g : unitTests)
    (hsupp : ∀ v ∉ E, g.val v=0) (hgn : completedTestFunctional unitTests g x=‖x‖)
    (A : I → Atom) (p σ : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (hσ : ∀ i, |σ i| ≤ 1) {e : ℝ} (he : 0 ≤ e)
    (hmean : ‖(∑ i, p i • (A i).inCore)-x‖ ≤ e)
    (hsigned : ‖(∑ i, (p i*σ i) • (A i).inCore)-y‖ ≤ e) :
    ‖completedTail unitTests E y‖ ≤
      2*e+(Real.sqrt 2+Real.sqrt 6)*Real.sqrt (1-‖x‖+e) := by
  let d := ∑ i, p i*(1-(A i).pairing g.val)
  let Z := ∑ i, p i • (A i).replacement g.val E
  let W := ∑ i, (p i*σ i) • (A i).replacement g.val E
  let U := ∑ i, p i • (A i).inCore
  let V := ∑ i, (p i*σ i) • (A i).inCore
  have hd : 0 ≤ d := Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) ((A i).defect g.property).1)
  have hdx : d ≤ 1-‖x‖+e := by
    have hh := completedTestFunctional_abs_le unitTests g (U-x)
    rw [map_sub,hgn] at hh
    have h_eval : completedTestFunctional unitTests g U=1-d := by
      dsimp only [U,d]
      simp only [map_sum,map_smul,smul_eq_mul]
      have heval (i : I) : completedTestFunctional unitTests g (A i).inCore=(A i).pairing g.val := by
        change completedTestFunctional unitTests g (coreLift (A i).vector)=_
        rw [test_coreLift,Atom.finitePairing_vector]
      simp only [heval]
      simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hp1]
      ring
    rw [h_eval] at hh
    have hnorm : ‖U-x‖ ≤ e := hmean
    have hab := (abs_le.mp hh).1
    linarith
  have hQx : completedTail unitTests E x=0 := by rw [completedTail_apply,hx,sub_self]
  have hU : ‖completedTail unitTests E U‖ ≤ e := by
    have hh := (core_tail_norm E hE (U-x)).trans hmean
    simpa only [map_sub,hQx,sub_zero] using hh
  have hV : ‖completedTail unitTests E V-completedTail unitTests E y‖ ≤ e := by
    rw [← map_sub]
    exact (core_tail_norm E hE (V-y)).trans hsigned
  have herrZ : ‖Z-completedTail unitTests E U‖ ≤ Real.sqrt (2*d) := by
    simpa only [mul_one] using mixture_replacement_error hE g.property A p (fun _ => 1) hp hp1 (by intro i; norm_num)
  have herrW : ‖W-completedTail unitTests E V‖ ≤ Real.sqrt (2*d) :=
    mixture_replacement_error hE g.property A p σ hp hp1 hσ
  have hZ : ‖Z‖ ≤ e+Real.sqrt (2*d) := by
    have hh := norm_add_le (Z-completedTail unitTests E U) (completedTail unitTests E U)
    rw [sub_add_cancel] at hh
    linarith
  have hWy : ‖W-completedTail unitTests E y‖ ≤ e+Real.sqrt (2*d) := by
    have hh := norm_add_le (W-completedTail unitTests E V)
      (completedTail unitTests E V-completedTail unitTests E y)
    rw [sub_add_sub_cancel] at hh
    linarith
  have hW : ‖W‖ ≤ Real.sqrt ((e+Real.sqrt (2*d))^2+4*d) := by
    apply (mixture_replacement_norm hE g.property hsupp A p σ hp hp1 hσ).trans
    apply Real.sqrt_le_sqrt
    change ‖Z‖^2+4*d ≤ _
    nlinarith [norm_nonneg Z,Real.sqrt_nonneg (2*d)]
  have htail : ‖completedTail unitTests E y‖ ≤
      e+Real.sqrt (2*d)+Real.sqrt ((e+Real.sqrt (2*d))^2+4*d) := by
    have hh := norm_add_le (completedTail unitTests E y-W) W
    rw [sub_add_cancel,norm_sub_rev] at hh
    linarith
  apply (htail.trans (finite_mixture_tail_scalar he hd)).trans
  have hcoef : 0 ≤ Real.sqrt 2+Real.sqrt 6 := by positivity
  simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdx) hcoef) (2*e)

end

lemma exists_atom_distribution (z : DualCore) (hz : ‖z‖ ≤ 1) {e : ℝ} (he : 0 < e) :
    ∃ (I : Type) (_ : Fintype I) (_ : Nonempty I) (p : I → ℝ) (A : I → Atom),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i)=1 ∧ ‖(∑ i, p i • (A i).inCore)-z‖ ≤ e := by
  have hzcl : z ∈ closure (convexHull ℝ (Set.range Atom.inCore)) := by
    rw [← core_atom_hull]
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz
  obtain ⟨w,hw,hzw⟩ := Metric.mem_closure_iff.mp hzcl e he
  obtain ⟨I,hI,p,v,hp,hp1,hv,hmean⟩ := mem_convexHull_iff_exists_fintype.mp hw
  let := hI
  have hne : Nonempty I := by
    by_contra hn
    have : IsEmpty I := not_nonempty_iff.mp hn
    simp at hp1
  choose A hA using hv
  refine ⟨I,hI,hne,p,A,hp,hp1,?_⟩
  simp_rw [hA]
  rw [hmean,norm_sub_rev]
  exact (show ‖z-w‖ < e by simpa only [dist_eq_norm] using hzw).le

/-- Both endpoint distributions are combined without requiring a common
finite index set, or assuming an attained atomic decomposition. -/
lemma endpoint_atom_distribution (x y : DualCore) (hp : ‖x+y‖ ≤ 1) (hm : ‖x-y‖ ≤ 1)
    {e : ℝ} (he : 0 < e) :
    ∃ (I : Type) (_ : Fintype I) (_ : Nonempty I) (p σ : I → ℝ) (A : I → Atom),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i)=1 ∧ (∀ i, |σ i| ≤ 1) ∧
      ‖(∑ i, p i • (A i).inCore)-x‖ ≤ e ∧
      ‖(∑ i, (p i*σ i) • (A i).inCore)-y‖ ≤ e := by
  obtain ⟨I,hI,hnI,p,A,hp0,hp1,hpa⟩ := exists_atom_distribution (x+y) hp he
  obtain ⟨J,hJ,hnJ,q,B,hq0,hq1,hqa⟩ := exists_atom_distribution (x-y) hm he
  let := hI
  let := hJ
  let := hnI
  let := hnJ
  let r : I ⊕ J → ℝ := Sum.elim (fun i => p i/2) (fun j => q j/2)
  let σ : I ⊕ J → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)
  let C : I ⊕ J → Atom := Sum.elim A B
  let U : DualCore := ∑ i, p i • (A i).inCore
  let V : DualCore := ∑ j, q j • (B j).inCore
  have hmean : (∑ k, r k • (C k).inCore)=(1/2 : ℝ) • (U+V) := by
    simp only [Fintype.sum_sum_type,r,C,Sum.elim_inl,Sum.elim_inr,smul_add,Finset.smul_sum,U,V]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> rw [smul_smul] <;> congr 1 <;> ring
  have hsigned : (∑ k, (r k*σ k) • (C k).inCore)=(1/2 : ℝ) • (U-V) := by
    simp only [Fintype.sum_sum_type,r,σ,C,Sum.elim_inl,Sum.elim_inr,mul_one,mul_neg_one,
      Finset.smul_sum,U,V,sub_eq_add_neg,← Finset.sum_neg_distrib,neg_smul,smul_add,smul_neg]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> simp only [smul_smul] <;> congr 1 <;> ring_nf
  refine ⟨I ⊕ J,inferInstance,inferInstance,r,σ,C,?_,?_,?_,?_,?_⟩
  · intro k
    cases k with
    | inl i => exact div_nonneg (hp0 i) (by norm_num)
    | inr j => exact div_nonneg (hq0 j) (by norm_num)
  · simp only [Fintype.sum_sum_type,r,Sum.elim_inl,Sum.elim_inr,← Finset.sum_div,hp1,hq1]
    norm_num
  · intro k
    cases k <;> norm_num [σ]
  · rw [hmean]
    have heq : (1/2 : ℝ) • (U+V)-x=(1/2 : ℝ) • ((U-(x+y))+(V-(x-y))) := by module
    rw [heq,norm_smul]
    norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hh := norm_add_le (U-(x+y)) (V-(x-y))
    change ‖U-(x+y)‖ ≤ e at hpa
    change ‖V-(x-y)‖ ≤ e at hqa
    linarith
  · rw [hsigned]
    have heq : (1/2 : ℝ) • (U-V)-y=(1/2 : ℝ) • ((U-(x+y))-(V-(x-y))) := by module
    rw [heq,norm_smul]
    norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hh := norm_sub_le (U-(x+y)) (V-(x-y))
    change ‖U-(x+y)‖ ≤ e at hpa
    change ‖V-(x-y)‖ ≤ e at hqa
    linarith

/-- The incomparable tail bound on the polar completion, without finite-support assumptions.
Its full-dual formulation follows from the core/full-dual identification. -/

theorem incomparable_tail_core {E : Finset Node} (hE : Initial (E : Set Node))
    (x y : DualCore) (hx : completedHead unitTests E x=x)
    (hp : ‖x+y‖ ≤ 1) (hm : ‖x-y‖ ≤ 1) :
    ‖completedTail unitTests E y‖ ≤ (Real.sqrt 2+Real.sqrt 6)*Real.sqrt (1-‖x‖) := by
  obtain ⟨g,hsupp,hgn⟩ := core_head_norming E hE x hx
  have hb {e : ℝ} (he : 0 < e) : ‖completedTail unitTests E y‖ ≤
      2*e+(Real.sqrt 2+Real.sqrt 6)*Real.sqrt (1-‖x‖+e) := by
    obtain ⟨I,hI,hnI,p,σ,A,hp0,hp1,hσ,hmean,hsigned⟩ := endpoint_atom_distribution x y hp hm he
    let := hI
    let := hnI
    exact finite_mixture_tail hE x y hx g hsupp hgn A p σ hp0 hp1 hσ he.le hmean hsigned
  have hc : Continuous (fun e : ℝ => 2*e+(Real.sqrt 2+Real.sqrt 6)*Real.sqrt (1-‖x‖+e)) := by
    fun_prop
  have ht := hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi (0:ℝ)))
  have hh := le_of_tendsto_of_tendsto (f := fun _ : ℝ => ‖completedTail unitTests E y‖)
    (b := 𝓝[Set.Ioi (0:ℝ)] 0) tendsto_const_nhds ht
    (Filter.Eventually.mono self_mem_nhdsWithin (fun e he => hb he))
  simpa only [mul_zero,add_zero,zero_add] using hh

end BoundedTreePotentials.Segments

end

end OAI
