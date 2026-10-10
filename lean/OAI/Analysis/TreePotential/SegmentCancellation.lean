import OAI.Analysis.TreePotential.SegmentHeads

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.Segments

lemma shortening_injective {Q : Type*} (qset : Finset Q)
    {g : Node → ℝ} (hg : IsUnitTest g) {F : Finset Segment} (hF : Incomparable F)
    (D : Q → Segment) (b : Q → ℝ)
    (hD : ∀ q ∈ qset, D q ∈ F) (hinj : Set.InjOn D (qset : Set Q))
    (hsign : ∀ q ∈ qset, (D q).eval g*b q ≤ 0)
    (hshort : ∀ q ∈ qset, ∃ R : Segment, R.start=(D q).start ∧
      R.eval g=(D q).eval g-b q) :
    2*(∑ q ∈ qset, |(D q).eval g*b q|) ≤ 1-(∑ S ∈ F, (S.eval g)^2) := by
  let G := qset.image D
  have hG : G ⊆ F := by
    intro S hS
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hS
    exact hD q hq
  have hi (S : Segment) (hS : S ∈ G) : ∃ q ∈ qset, D q=S := Finset.mem_image.mp hS
  let c : Segment → ℝ := fun S => if hS : S ∈ G then b (hi S hS).choose else 0
  have hc (q : Q) (hq : q ∈ qset) : c (D q)=b q := by
    have hqG : D q ∈ G := Finset.mem_image.mpr ⟨q,hq,rfl⟩
    dsimp only [c]
    rw [dite_eq_left hqG]
    congr 1
    exact hinj (hi _ hqG).choose_spec.1 hq (hi _ hqG).choose_spec.2
  have hex (S : Segment) : ∃ R : Segment, R.start=S.start ∧ R.eval g=S.eval g-c S := by
    by_cases hS : S ∈ G
    · obtain ⟨q,hq,rfl⟩ := hi S hS
      simpa only [hc q hq] using hshort q hq
    · refine ⟨S,rfl,?_⟩
      simp [c,hS]
  choose R hR using hex
  have hh := shortening_loss hg hF R c (fun S _ => (hR S).1) (fun S _ => (hR S).2) (by
    intro S hS
    by_cases hSG : S ∈ G
    · obtain ⟨q,hq,rfl⟩ := hi S hSG
      rw [hc q hq]
      exact hsign q hq
    · simp [c,hSG])
  have he : (∑ S ∈ F, |S.eval g*c S|) = ∑ q ∈ qset, |(D q).eval g*b q| := by
    calc
      _ = ∑ S ∈ G, |S.eval g*c S| := by
        symm
        apply Finset.sum_subset hG
        intro S hS hSG
        simp [c,hSG]
      _ = ∑ q ∈ qset, |(D q).eval g*c (D q)| := Finset.sum_image hinj
      _ = _ := Finset.sum_congr rfl (fun q hq => by rw [hc q hq])
  rwa [he] at hh

namespace Atom

def sees (A : Atom) (q : Node) : Prop := ∃ S ∈ A.family, q ∈ S.nodes

def original (A : Atom) (q : Node) : Segment :=
  if h : A.sees q then h.choose else Segment.singleton q

def exitCoeff (A : Atom) (g : Node → ℝ) (q : Node) : ℝ :=
  if A.sees q then (A.original q).eval g else 0

lemma original_spec (A : Atom) {q : Node} (hq : A.sees q) :
    A.original q ∈ A.family ∧ q ∈ (A.original q).nodes := by
  simp only [original, dite_eq_left hq]
  exact hq.choose_spec

lemma original_eq (A : Atom) {S : Segment} (hS : S ∈ A.family) {q : Node}
    (hq : q ∈ S.nodes) : A.original q=S := by
  have hsee : A.sees q := ⟨S,hS,hq⟩
  obtain ⟨hmem,hnode⟩ := A.original_spec hsee
  by_contra hne
  exact Finset.disjoint_left.mp (incomparable_disjoint A.incomparable hmem hS hne) hnode hq

lemma exitCoeff_eq (A : Atom) (g : Node → ℝ) {S : Segment} (hS : S ∈ A.family) {q : Node}
    (hq : q ∈ S.nodes) : A.exitCoeff g q=S.eval g := by
  rw [exitCoeff, ite_eq_left (show A.sees q from ⟨S,hS,hq⟩), A.original_eq hS hq]

lemma exitCoeff_ne_zero (A : Atom) {g : Node → ℝ} {q : Node} (hq : A.exitCoeff g q ≠ 0) :
    A.sees q := by
  by_contra hn
  exact hq (by simp [exitCoeff,hn])

lemma original_injective {C : Set Node} (A : Atom) {Q : Finset Node}
    (hQ : ∀ q ∈ Q, IsExit C q) (hsee : ∀ q ∈ Q, A.sees q) :
    Set.InjOn A.original (Q : Set Node) := by
  intro q hq r hr he
  by_contra hne
  have hqn := (A.original_spec (hsee q hq)).2
  have hrn := (A.original_spec (hsee r hr)).2
  rw [← he] at hrn
  have hh := prefix_chain (((A.original q).mem_nodes q).mp hqn).2
    (((A.original q).mem_nodes r).mp hrn).2
  exact hh.elim (exits_incomparable (hQ q hq) (hQ r hr) hne).1
    (exits_incomparable (hQ q hq) (hQ r hr) hne).2

/-- The shorter-start half of opposite-exit cancellation. -/
lemma early_cancellation {C : Set Node} (hC : Initial C) {g : Node → ℝ}
    (hg : IsUnitTest g) (hsupp : ∀ v ∉ C, g v=0) (A B : Atom) (Q : Finset Node)
    (hQ : ∀ q ∈ Q, IsExit C q)
    (hop : ∀ q ∈ Q, A.exitCoeff g q*B.exitCoeff g q < 0)
    (hearly : ∀ q ∈ Q, Prefix (A.original q).start (B.original q).start ∧
      (A.original q).start ≠ (B.original q).start) :
    2*(∑ q ∈ Q, |A.exitCoeff g q*B.exitCoeff g q|) ≤
      1-(∑ S ∈ A.family, (S.eval g)^2) := by
  have hAn (q : Node) (hq : q ∈ Q) : A.exitCoeff g q ≠ 0 := by
    intro he
    have hh := hop q hq
    rw [he,zero_mul] at hh
    linarith
  have hBn (q : Node) (hq : q ∈ Q) : B.exitCoeff g q ≠ 0 := by
    intro he
    have hh := hop q hq
    rw [he,mul_zero] at hh
    linarith
  have hAs q hq := A.original_spec (A.exitCoeff_ne_zero (hAn q hq))
  have hBs q hq := B.original_spec (B.exitCoeff_ne_zero (hBn q hq))
  have hAe (q : Node) (hq : q ∈ Q) : A.exitCoeff g q=(A.original q).eval g :=
    A.exitCoeff_eq g (hAs q hq).1 (hAs q hq).2
  have hBe (q : Node) (hq : q ∈ Q) : B.exitCoeff g q=(B.original q).eval g :=
    B.exitCoeff_eq g (hBs q hq).1 (hBs q hq).2
  have hh := shortening_injective Q hg A.incomparable A.original (B.exitCoeff g)
    (fun q hq => (hAs q hq).1)
    (A.original_injective hQ (fun q hq => A.exitCoeff_ne_zero (hAn q hq)))
    (fun q hq => by rw [← hAe q hq]; exact (hop q hq).le) (by
      intro q hq
      obtain ⟨R,hstart,heval⟩ := Segment.shorten_at_exit hC hsupp (A.original q) (B.original q)
        (hAs q hq).2 (hBs q hq).2 (hQ q hq).1 (hearly q hq).1 (hearly q hq).2
      exact ⟨R,hstart,by rw [hBe q hq]; exact heval⟩)
  convert hh using 2
  apply Finset.sum_congr rfl
  intro q hq
  rw [hAe q hq]

end Atom
end BoundedTreePotentials.Segments

namespace BoundedTreePotentials.Segments.Atom

lemma opposite_starts {C : Set Node} (hC : Initial C) {g : Node → ℝ}
    (hsupp : ∀ v ∉ C, g v=0) (A B : Atom) {q : Node} (hq : IsExit C q)
    (hop : A.exitCoeff g q*B.exitCoeff g q < 0) :
    (Prefix (A.original q).start (B.original q).start ∨
      Prefix (B.original q).start (A.original q).start) ∧
    (A.original q).start ≠ (B.original q).start := by
  have hnA : A.exitCoeff g q ≠ 0 := by intro he; rw [he,zero_mul] at hop; exact (lt_irrefl _ hop)
  have hnB : B.exitCoeff g q ≠ 0 := by intro he; rw [he,mul_zero] at hop; exact (lt_irrefl _ hop)
  obtain ⟨hAm,hAq⟩ := A.original_spec (A.exitCoeff_ne_zero hnA)
  obtain ⟨hBm,hBq⟩ := B.original_spec (B.exitCoeff_ne_zero hnB)
  refine ⟨prefix_chain (((A.original q).mem_nodes q).mp hAq).1
    (((B.original q).mem_nodes q).mp hBq).1,?_⟩
  intro hstart
  have he : A.exitCoeff g q=B.exitCoeff g q := by
    rw [A.exitCoeff_eq g hAm hAq,B.exitCoeff_eq g hBm hBq,
      Segment.eval_to_exit hC hsupp _ hAq hq.1,Segment.eval_to_exit hC hsupp _ hBq hq.1]
    congr 2
  rw [he] at hop
  nlinarith [sq_nonneg (B.exitCoeff g q)]

/-- Opposite coefficients at any finite set of actual exits consume exactly
both unused squared-evaluation budgets, hence the two atom defects. -/
theorem cancellation {C : Set Node} (hC : Initial C) {g : Node → ℝ}
    (hg : IsUnitTest g) (hsupp : ∀ v ∉ C, g v=0) (A B : Atom) (Q : Finset Node)
    (hQ : ∀ q ∈ Q, IsExit C q) :
    (∑ q ∈ Q, oppositeProduct (A.exitCoeff g q) (B.exitCoeff g q)) ≤
      (1-A.pairing g)+(1-B.pairing g) := by
  let H := Q.filter (fun q => A.exitCoeff g q*B.exitCoeff g q < 0)
  let E := H.filter (fun q => Prefix (A.original q).start (B.original q).start)
  let L := H.filter (fun q => ¬Prefix (A.original q).start (B.original q).start)
  have hH (q : Node) (hq : q ∈ H) : q ∈ Q ∧ A.exitCoeff g q*B.exitCoeff g q < 0 :=
    Finset.mem_filter.mp hq
  have hE (q : Node) (hq : q ∈ E) := Finset.mem_filter.mp hq
  have hL (q : Node) (hq : q ∈ L) := Finset.mem_filter.mp hq
  have h1 := A.early_cancellation hC hg hsupp B E
    (fun q hq => hQ q (hH q (hE q hq).1).1)
    (fun q hq => (hH q (hE q hq).1).2) (by
      intro q hq
      exact ⟨(hE q hq).2,(opposite_starts hC hsupp A B
        (hQ q (hH q (hE q hq).1).1) (hH q (hE q hq).1).2).2⟩)
  have h2 := B.early_cancellation hC hg hsupp A L
    (fun q hq => hQ q (hH q (hL q hq).1).1)
    (fun q hq => by simpa only [mul_comm] using (hH q (hL q hq).1).2) (by
      intro q hq
      have hh := opposite_starts hC hsupp A B (hQ q (hH q (hL q hq).1).1)
        (hH q (hL q hq).1).2
      exact ⟨hh.1.resolve_left (hL q hq).2,hh.2.symm⟩)
  have hsplit : (∑ q ∈ E, |A.exitCoeff g q*B.exitCoeff g q|)+
      (∑ q ∈ L, |B.exitCoeff g q*A.exitCoeff g q|) =
      ∑ q ∈ Q, oppositeProduct (A.exitCoeff g q) (B.exitCoeff g q) := by
    simp only [mul_comm (B.exitCoeff g _) (A.exitCoeff g _)]
    rw [Finset.sum_filter_add_sum_filter_not]
    simp only [H, Finset.sum_filter, oppositeProduct_eq]
  have hdA := (A.defect hg).2.2
  have hdB := (B.defect hg).2.2
  linarith

end BoundedTreePotentials.Segments.Atom

namespace BoundedTreePotentials.Segments

lemma finitePairing_filter (C : Set Node) [DecidablePred (fun v => v ∈ C)] (g : Node → ℝ) (z : Node →₀ ℝ) :
    finitePairing g (Finsupp.filter (fun v => v ∈ C) z) = finitePairing (C.indicator g) z := by
  rw [finitePairing_apply]
  simp only [Finsupp.support_filter, Finset.sum_filter, Finsupp.filter_apply,
    finitePairing_apply, Set.indicator_apply]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs <;> simp_all

lemma finitePairing_tail (C : Set Node) [DecidablePred (fun v => v ∈ C)] (g : Node → ℝ) (z : Node →₀ ℝ) :
    finitePairing g (z-Finsupp.filter (fun v => v ∈ C) z) = finitePairing (Cᶜ.indicator g) z := by
  have he : z-Finsupp.filter (fun v => v ∈ C) z = Finsupp.filter (fun v => v ∈ Cᶜ) z := by
    ext v
    simp only [Finsupp.sub_apply,Finsupp.filter_apply,Set.mem_compl_iff]
    split_ifs <;> simp
  rw [he]
  exact finitePairing_filter Cᶜ g z

lemma finitePairing_filter_finset (E : Finset Node) (g : Node → ℝ) (z : Node →₀ ℝ) :
    finitePairing g (Finsupp.filter (fun v => v ∈ E) z)=finitePairing ((E : Set Node).indicator g) z := by
  simp only [finitePairing_apply,Finsupp.support_filter,Finset.sum_filter,Finsupp.filter_apply,
    Set.indicator_apply,Finset.mem_coe]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs <;> simp_all

lemma finitePairing_tail_finset (E : Finset Node) (g : Node → ℝ) (z : Node →₀ ℝ) :
    finitePairing g (z-Finsupp.filter (fun v => v ∈ E) z)=finitePairing ((E : Set Node)ᶜ.indicator g) z := by
  rw [map_sub,finitePairing_filter_finset]
  simp only [finitePairing_apply,← Finset.sum_sub_distrib,Set.indicator_apply,
    Set.mem_compl_iff,Finset.mem_coe]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs <;> simp_all

lemma core_head_norm (E : Finset Node) (hE : Initial (E : Set Node)) (x : DualCore) :
    ‖completedHead unitTests E x‖ ≤ ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le (completedHead unitTests E).continuous.norm continuous_norm) ?_
  intro z
  rw [completedHead_coe,UniformSpace.Completion.norm_coe,UniformSpace.Completion.norm_coe]
  rw [norm_testVector_equiv, norm_testVector_equiv, LinearEquiv.apply_symm_apply]
  apply ciSup_le
  intro g
  rw [finitePairing_filter_finset E g.val]
  exact finitePairing_le_testNorm unitTests ⟨_,unit_head hE g.property⟩ ((testVectorEquiv unitTests) z)

lemma core_tail_norm (E : Finset Node) (hE : Initial (E : Set Node)) (x : DualCore) :
    ‖completedTail unitTests E x‖ ≤ ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le (completedTail unitTests E).continuous.norm continuous_norm) ?_
  intro z
  rw [completedTail_coe,UniformSpace.Completion.norm_coe,UniformSpace.Completion.norm_coe]
  rw [norm_testVector_equiv, norm_testVector_equiv, LinearEquiv.apply_symm_apply]
  apply ciSup_le
  intro g
  rw [finitePairing_tail_finset E g.val]
  exact finitePairing_le_testNorm unitTests ⟨_,unit_tail hE g.property⟩ ((testVectorEquiv unitTests) z)

lemma functionalCoeffs_unit (φ : DualCore →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) :
    IsUnitTest (functionalCoeffs φ) := by
  rw [unit_iff_pairing_atoms]
  intro A
  rw [← functional_atom]
  have hh := φ.le_of_opNorm_le hφ A.inCore
  exact (by simpa only [Real.norm_eq_abs,one_mul] using hh : |φ A.inCore| ≤ ‖A.inCore‖).trans A.norm_inCore

lemma functionalCoeffs_eq (φ : DualCore →L[ℝ] ℝ) (hφ : ‖φ‖ ≤ 1) (x : DualCore) :
    completedTestFunctional unitTests ⟨functionalCoeffs φ,functionalCoeffs_unit φ hφ⟩ x=φ x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (completedTestFunctional unitTests _).continuous φ.continuous) ?_
  intro z
  rw [completedTestFunctional_coe]
  exact (functional_coreLift φ ((testVectorEquiv unitTests) z)).symm

lemma core_test_head (E : Finset Node) (hE : Initial (E : Set Node)) (g : unitTests) (x : DualCore) :
    completedTestFunctional unitTests ⟨(E : Set Node).indicator g.val,unit_head hE g.property⟩ x =
      completedTestFunctional unitTests g (completedHead unitTests E x) := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (completedTestFunctional unitTests _).continuous
      ((completedTestFunctional unitTests g).continuous.comp (completedHead unitTests E).continuous)) ?_
  intro z
  rw [completedHead_coe,completedTestFunctional_coe,completedTestFunctional_coe]
  change finitePairing ((E : Set Node).indicator g.val) ((testVectorEquiv unitTests) z) =
    finitePairing g.val (Finsupp.filter (fun v => v ∈ E) ((testVectorEquiv unitTests) z))
  exact (finitePairing_filter_finset E g.val ((testVectorEquiv unitTests) z)).symm

lemma core_head_norming (E : Finset Node) (hE : Initial (E : Set Node)) (x : DualCore)
    (hx : completedHead unitTests E x=x) :
    ∃ g : unitTests, (∀ v ∉ E, g.val v=0) ∧ completedTestFunctional unitTests g x=‖x‖ := by
  by_cases hn : ‖x‖=0
  · have hx0 := norm_eq_zero.mp hn
    refine ⟨⟨0,unit_zero⟩,by simp,?_⟩
    simp [hx0]
  · obtain ⟨φ,hφ,hφx⟩ := exists_dual_vector ℝ x hn
    let g : unitTests := ⟨functionalCoeffs φ,functionalCoeffs_unit φ hφ.le⟩
    refine ⟨⟨(E : Set Node).indicator g.val,unit_head hE g.property⟩,?_,?_⟩
    · intro v hv
      exact Set.indicator_of_notMem hv _
    · rw [core_test_head E hE g x, hx]
      exact (functionalCoeffs_eq φ hφ.le x).trans hφx

end BoundedTreePotentials.Segments

end

end OAI
