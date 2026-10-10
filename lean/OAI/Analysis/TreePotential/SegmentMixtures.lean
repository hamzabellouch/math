import OAI.Analysis.TreePotential.SegmentCancellation

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.Segments

lemma coreLift_norm (z : Node →₀ ℝ) : ‖coreLift z‖=testNorm unitTests z := by
  exact UniformSpace.Completion.norm_coe ((testVectorEquiv unitTests).symm z)

lemma norm_segment_sum (F : Finset Segment) (hF : Incomparable F) (a : Segment → ℝ) :
    ‖∑ S ∈ F, a S • coreLift (segmentVector S)‖ ≤ Real.sqrt (∑ S ∈ F, (a S)^2) := by
  have he : (∑ S ∈ F, a S • coreLift (segmentVector S)) =
      coreLift (∑ S ∈ F, a S • segmentVector S) := by simp only [map_sum,map_smul]
  rw [he,coreLift_norm]
  apply ciSup_le
  intro g
  simp only [map_sum,map_smul,smul_eq_mul,finitePairing_segmentVector]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq F a (fun S => S.eval g.val)
  have hn : 0 ≤ ∑ S ∈ F, (a S)^2 := Finset.sum_nonneg (fun S _ => sq_nonneg _)
  have hg := g.property F hF
  have hmul := mul_le_mul_of_nonneg_left hg hn
  have hs : (∑ S ∈ F, a S*S.eval g.val)^2 ≤ ∑ S ∈ F, (a S)^2 := by nlinarith
  have hr := Real.sq_sqrt hn
  have hp := Real.sqrt_nonneg (∑ S ∈ F, (a S)^2)
  rw [abs_le]
  constructor <;> nlinarith

namespace Atom

def replaced (A : Atom) (g : Node → ℝ) : DualCore :=
  ∑ S ∈ A.family, S.eval g • coreLift (segmentVector S)

def replacement (A : Atom) (g : Node → ℝ) (E : Finset Node) : DualCore :=
  completedTail unitTests E (A.replaced g)

lemma inCore_sum (A : Atom) : A.inCore=∑ S ∈ A.family, A.coeff S • coreLift (segmentVector S) := by
  change coreLift A.vector = _
  simp only [Atom.vector,map_sum,map_smul]

lemma replacement_error (A : Atom) {g : Node → ℝ} (hg : IsUnitTest g)
    (E : Finset Node) (hE : Initial (E : Set Node)) :
    ‖A.replacement g E-completedTail unitTests E A.inCore‖ ≤ Real.sqrt (2*(1-A.pairing g)) := by
  rw [replacement,← map_sub]
  apply (core_tail_norm E hE _).trans
  have he : A.replaced g-A.inCore =
      ∑ S ∈ A.family, (S.eval g-A.coeff S) • coreLift (segmentVector S) := by
    rw [replaced,inCore_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    exact (sub_smul ..).symm
  rw [he]
  apply (norm_segment_sum A.family A.incomparable _).trans
  apply Real.sqrt_le_sqrt
  simpa only [sub_sq_comm] using (A.defect hg).2.1

end Atom

lemma Segment.ext {S T : Segment} (hs : S.start=T.start) (hf : S.finish=T.finish) : S=T := by
  cases S
  cases T
  dsimp only at hs hf
  cases hs
  cases hf
  rfl

def Segment.suffixAt (S : Segment) (q : Node) : Segment :=
  if h : Prefix q S.finish then ⟨q,S.finish,h⟩ else Segment.singleton q

@[simp] lemma Segment.suffixAt_start (S : Segment) (q : Node) : (S.suffixAt q).start=q := by
  unfold suffixAt
  split_ifs <;> rfl

lemma Segment.suffixAt_finish (S : Segment) {q : Node} (hq : q ∈ S.nodes) :
    (S.suffixAt q).finish=S.finish := by
  simp only [suffixAt,dite_eq_left ((S.mem_nodes q).mp hq).2]

lemma Segment.suffixAt_eq (S R : Segment) (hf : R.finish=S.finish) : S.suffixAt R.start=R := by
  apply Segment.ext (S.suffixAt_start R.start)
  simp only [suffixAt,dite_eq_left (by rw [← hf]; exact R.extends_to : Prefix R.start S.finish)]
  exact hf.symm

def segmentCutVector (E : Finset Node) (S : Segment) : Node →₀ ℝ :=
  ∑ v ∈ S.nodes.filter (fun v => v ∉ E), Finsupp.single v 1

lemma cutVector_apply (E : Finset Node) (S : Segment) (v : Node) :
    segmentCutVector E S v=if v ∈ S.nodes ∧ v ∉ E then 1 else 0 := by
  simp [segmentCutVector,Finsupp.finsetSum_apply,Finsupp.single_apply,eq_comm]

lemma core_tail_segment (E : Finset Node) (S : Segment) :
    completedTail unitTests E (coreLift (segmentVector S))=coreLift (segmentCutVector E S) := by
  rw [show coreLift (segmentVector S) =
    (((testVectorEquiv unitTests).symm (segmentVector S) : TestVector unitTests) : DualCore) from rfl,
    completedTail_coe]
  apply congrArg (fun z => coreLift z)
  ext v
  simp only [Finsupp.sub_apply,Finsupp.filter_apply,cutVector_apply]
  split_ifs <;> simp_all

lemma cutVector_empty (E : Finset Node) (S : Segment)
    (hn : ¬(S.nodes.filter (fun v => v ∉ E)).Nonempty) : segmentCutVector E S=0 := by
  simp only [segmentCutVector,Finset.not_nonempty_iff_eq_empty.mp hn,Finset.sum_empty]

lemma cutVector_segment (E : Finset Node) (S R : Segment)
    (hR : R.nodes=S.nodes.filter (fun v => v ∉ E)) : segmentCutVector E S=segmentVector R := by
  simp only [segmentCutVector,segmentVector,hR]

lemma eval_ne_zero_start {C : Set Node} (hC : Initial C) {g : Node → ℝ}
    (hg : ∀ v ∉ C, g v=0) (S : Segment) (hp : S.eval g ≠ 0) : S.start ∈ C := by
  by_contra hs
  apply hp
  apply Finset.sum_eq_zero
  intro v hv
  exact hg v (initial_complement hC hs ((S.mem_nodes v).mp hv).1)

lemma Segment.exit_unique {C : Set Node} (S : Segment) {q r : Node}
    (hq : IsExit C q) (hr : IsExit C r) (hqS : q ∈ S.nodes) (hrS : r ∈ S.nodes) : q=r := by
  by_contra hn
  have hh := prefix_chain ((S.mem_nodes q).mp hqS).2 ((S.mem_nodes r).mp hrS).2
  exact hh.elim (exits_incomparable hq hr hn).1 (exits_incomparable hq hr hn).2

lemma segment_exit_decomposition {E : Finset Node} (hE : Initial (E : Set Node))
    {g : Node → ℝ} (hg : ∀ v ∉ E, g v=0) (S : Segment) (Q : Finset Node)
    (hQ : ∀ q ∈ Q, IsExit (E : Set Node) q)
    (hcover : ∀ q ∈ S.nodes, IsExit (E : Set Node) q → q ∈ Q) :
    (∑ q ∈ Q, if q ∈ S.nodes then S.eval g • coreLift (segmentVector (S.suffixAt q)) else 0)=
      S.eval g • completedTail unitTests E (coreLift (segmentVector S)) := by
  by_cases hp : S.eval g=0
  · simp [hp]
  by_cases hn : (S.nodes.filter (fun v => v ∉ E)).Nonempty
  · obtain ⟨R,hf,hs,hR,hexit⟩ := S.tail_exit hE (eval_ne_zero_start hE hg S hp) (by simpa using hn)
    have hq : R.start ∈ Q := hcover R.start hs hexit
    rw [Finset.sum_eq_single_of_mem R.start hq]
    · rw [ite_eq_left hs, core_tail_segment,cutVector_segment E S R (by simpa using hR), S.suffixAt_eq R hf]
    · intro q hq hne
      have hnot : q ∉ S.nodes := fun hqs => hne (S.exit_unique (hQ q hq) hexit hqs hs)
      simp [hnot]
  · rw [core_tail_segment,cutVector_empty E S hn,map_zero,smul_zero]
    apply Finset.sum_eq_zero
    intro q hq
    have hnot : q ∉ S.nodes := fun hqs => hn ⟨q,Finset.mem_filter.mpr ⟨hqs,(hQ q hq).1⟩⟩
    simp [hnot]

namespace Atom

def terminal (A : Atom) (q : Node) : Segment := (A.original q).suffixAt q

@[simp] lemma terminal_start (A : Atom) (q : Node) : (A.terminal q).start=q := Segment.suffixAt_start ..

lemma exit_piece_sum (A : Atom) (g : Node → ℝ) (q : Node) :
    A.exitCoeff g q • coreLift (segmentVector (A.terminal q)) =
      ∑ S ∈ A.family, if q ∈ S.nodes then S.eval g • coreLift (segmentVector (S.suffixAt q)) else 0 := by
  by_cases hq : A.sees q
  · obtain ⟨hS,hnode⟩ := A.original_spec hq
    rw [Finset.sum_eq_single_of_mem (A.original q) hS,ite_eq_left hnode,A.exitCoeff_eq g hS hnode]
    · rfl
    · intro T hT hne
      have hn : q ∉ T.nodes := fun hnodeT => hne (A.original_eq hT hnodeT).symm
      simp [hn]
  · have hn : ∀ S ∈ A.family, q ∉ S.nodes := by simpa only [sees,not_exists,not_and] using hq
    simp only [exitCoeff,ite_eq_right hq,zero_smul]
    symm
    exact Finset.sum_eq_zero (fun S hS => by simp [hn S hS])

lemma replacement_exits {E : Finset Node} (hE : Initial (E : Set Node))
    {g : Node → ℝ} (hg : ∀ v ∉ E, g v=0) (A : Atom) (Q : Finset Node)
    (hQ : ∀ q ∈ Q, IsExit (E : Set Node) q)
    (hcover : ∀ S ∈ A.family, ∀ q ∈ S.nodes, IsExit (E : Set Node) q → q ∈ Q) :
    A.replacement g E=∑ q ∈ Q, A.exitCoeff g q • coreLift (segmentVector (A.terminal q)) := by
  simp only [exit_piece_sum]
  rw [Finset.sum_comm]
  simp only [replacement,replaced,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro S hS
  exact (segment_exit_decomposition hE hg S Q hQ (hcover S hS)).symm

end Atom

lemma core_norm_le_tests (x : DualCore) (R : ℝ)
    (h : ∀ g : unitTests, |completedTestFunctional unitTests g x| ≤ R) : ‖x‖ ≤ R := by
  rw [completed_tests_norming]
  exact ciSup_le (fun g => (le_abs_self _).trans (h g))

lemma test_coreLift (g : unitTests) (z : Node →₀ ℝ) :
    completedTestFunctional unitTests g (coreLift z)=finitePairing g.val z :=
  completedTestFunctional_coe unitTests g ((testVectorEquiv unitTests).symm z)

lemma unit_exit_family {C : Set Node} {g : Node → ℝ} (hg : IsUnitTest g)
    (Q : Finset Node) (hQ : ∀ q ∈ Q, IsExit C q) (R : Node → Segment)
    (hR : ∀ q ∈ Q, (R q).start=q) : (∑ q ∈ Q, ((R q).eval g)^2) ≤ 1 := by
  have hinj : Set.InjOn R (Q : Set Node) := by
    intro q hq r hr he
    exact (hR q hq).symm.trans ((congrArg Segment.start he).trans (hR r hr))
  have hi : Incomparable (Q.image R) := by
    rintro S hS T hT hne
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hT
    rw [hR q hq,hR r hr]
    exact exits_incomparable (hQ q hq) (hQ r hr) (fun he => hne (congrArg R he))
  have hh := hg (Q.image R) hi
  rwa [Finset.sum_image hinj] at hh

lemma norm_exit_mixture {I : Type*} [Fintype I] [Nonempty I] {C : Set Node}
    (Q : Finset Node) (hQ : ∀ q ∈ Q, IsExit C q) (R : I → Node → Segment)
    (hR : ∀ i q, (R i q).start=q) (p σ : I → ℝ) (r : I → Node → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hσ : ∀ i, |σ i| ≤ 1) :
    ‖∑ i, (p i*σ i) • (∑ q ∈ Q, r i q • coreLift (segmentVector (R i q)))‖ ≤
      Real.sqrt (∑ q ∈ Q, (∑ i, p i*|r i q|)^2) := by
  apply core_norm_le_tests
  intro g
  have hmax (q : Node) : ∃ i : I, ∀ j : I, |(R j q).eval g.val| ≤ |(R i q).eval g.val| := by
    obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun i : I => |(R i q).eval g.val|) Finset.univ_nonempty
    exact ⟨i,fun j => hi j (Finset.mem_univ j)⟩
  choose im him using hmax
  let L : Node → ℝ := fun q => |(R (im q) q).eval g.val|
  let b : Node → ℝ := fun q => ∑ i, p i*|r i q|
  have hL : (∑ q ∈ Q, (L q)^2) ≤ 1 := by
    simpa only [L,sq_abs] using unit_exit_family g.property Q hQ (fun q => R (im q) q) (fun q _ => hR (im q) q)
  have hb : ∀ q, 0 ≤ b q := fun q => Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (abs_nonneg _))
  have hL0 : ∀ q, 0 ≤ L q := fun q => abs_nonneg _
  have he : completedTestFunctional unitTests g
      (∑ i, (p i*σ i) • (∑ q ∈ Q, r i q • coreLift (segmentVector (R i q)))) =
      ∑ q ∈ Q, ∑ i, p i*σ i*r i q*(R i q).eval g.val := by
    simp only [map_sum,map_smul,smul_eq_mul,test_coreLift,finitePairing_segmentVector,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  have hsum : |∑ q ∈ Q, ∑ i, p i*σ i*r i q*(R i q).eval g.val| ≤ ∑ q ∈ Q, b q*L q := by
    apply (Finset.abs_sum_le_sum_abs _ Q).trans
    apply Finset.sum_le_sum
    intro q hq
    calc
      |∑ i, p i*σ i*r i q*(R i q).eval g.val| ≤
          ∑ i, |p i*σ i*r i q*(R i q).eval g.val| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, p i*|r i q| *L q := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [abs_mul,abs_of_nonneg (hp i)]
        have h1 := mul_le_mul_of_nonneg_left (hσ i) (hp i)
        have h2 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (r i q))
        simp only [mul_one] at h2
        have h3 := mul_le_mul h2 (him q i) (abs_nonneg _) (mul_nonneg (hp i) (abs_nonneg _))
        simpa only [mul_one,L] using h3
      _ = b q*L q := by rw [Finset.sum_mul]
  apply hsum.trans
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Q b L
  have hn : 0 ≤ ∑ q ∈ Q, (b q)^2 := Finset.sum_nonneg (fun q _ => sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hL hn
  have hs := Real.sq_sqrt hn
  have hs0 := Real.sqrt_nonneg (∑ q ∈ Q, (b q)^2)
  change (∑ q ∈ Q, b q*L q) ≤ Real.sqrt (∑ q ∈ Q, (b q)^2)
  nlinarith

lemma eval_antichainTest (S : Segment) (Q : Finset Node) (a : Node → ℝ) :
    S.eval ((Q : Set Node).indicator a)=∑ q ∈ Q, if q ∈ S.nodes then a q else 0 := by
  simp only [Segment.eval,Set.indicator_apply,Finset.mem_coe]
  rw [← Finset.sum_filter,← Finset.sum_filter]
  congr 1
  ext v
  simp [and_comm]

lemma unit_antichainTest {C : Set Node} (Q : Finset Node) (hQ : ∀ q ∈ Q, IsExit C q)
    (a : Node → ℝ) (ha : (∑ q ∈ Q, (a q)^2) ≤ 1) :
    IsUnitTest ((Q : Set Node).indicator a) := by
  intro F hF
  have hsq (S : Segment) : (S.eval ((Q : Set Node).indicator a))^2=
      ∑ q ∈ Q, if q ∈ S.nodes then (a q)^2 else 0 := by
    rw [eval_antichainTest]
    by_cases hex : ∃ q ∈ Q, q ∈ S.nodes
    · obtain ⟨q,hq,hqS⟩ := hex
      have hn : ∀ r ∈ Q, r ≠ q → r ∉ S.nodes := by
        intro r hr hne hrS
        exact hne (S.exit_unique (hQ r hr) (hQ q hq) hrS hqS)
      rw [Finset.sum_eq_single_of_mem q hq (fun r hr hne => by simp [hn r hr hne]),
        Finset.sum_eq_single_of_mem q hq (fun r hr hne => by simp [hn r hr hne])]
      simp [hqS]
    · have hn : ∀ q ∈ Q, q ∉ S.nodes := by simpa only [not_exists,not_and] using hex
      have hz1 : (∑ q ∈ Q, if q ∈ S.nodes then a q else 0)=0 :=
        Finset.sum_eq_zero (fun q hq => by simp [hn q hq])
      have hz2 : (∑ q ∈ Q, if q ∈ S.nodes then (a q)^2 else 0)=0 :=
        Finset.sum_eq_zero (fun q hq => by simp [hn q hq])
      rw [hz1,hz2]
      norm_num
  simp only [hsq]
  rw [Finset.sum_comm]
  apply (Finset.sum_le_sum ?_).trans ha
  intro q hq
  by_cases hex : ∃ S ∈ F, q ∈ S.nodes
  · obtain ⟨S,hS,hqS⟩ := hex
    rw [Finset.sum_eq_single_of_mem S hS]
    · simp [hqS]
    · intro T hT hne
      have hn : q ∉ T.nodes := fun hqT =>
        Finset.disjoint_left.mp (incomparable_disjoint hF hT hS hne) hqT hqS
      simp [hn]
  · have hn : ∀ S ∈ F, q ∉ S.nodes := by simpa only [not_exists,not_and] using hex
    rw [Finset.sum_eq_zero (fun S hS => by simp [hn S hS])]
    exact sq_nonneg _

lemma coordinate_coreLift (v : Node) (z : Node →₀ ℝ) :
    coordinateFunctional unitTests v (coreLift z)=z v :=
  coordinateFunctional_coe unitTests v ((testVectorEquiv unitTests).symm z)

lemma head_test_sum (Q : Finset Node) (a : Node → ℝ)
    (ha : IsUnitTest ((Q : Set Node).indicator a)) (x : DualCore) :
    completedTestFunctional unitTests ⟨(Q : Set Node).indicator a,ha⟩ x =
      ∑ q ∈ Q, a q*coordinateFunctional unitTests q x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (completedTestFunctional unitTests _).continuous
      (continuous_finsetSum _ (fun q _ => continuous_const.mul (coordinateFunctional unitTests q).continuous))) ?_
  intro z
  simp only [completedTestFunctional_coe,coordinateFunctional_coe]
  change finitePairing ((Q : Set Node).indicator a) ((testVectorEquiv unitTests) z) = _
  rw [← finitePairing_filter_finset Q a,finiteHead_eq_sum]
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro q hq
  simp [finitePairing,mul_comm]

lemma antichain_coordinates_sq {C : Set Node} (Q : Finset Node) (hQ : ∀ q ∈ Q, IsExit C q)
    (x : DualCore) : (∑ q ∈ Q, (coordinateFunctional unitTests q x)^2) ≤ ‖x‖^2 := by
  let B := ∑ q ∈ Q, (coordinateFunctional unitTests q x)^2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun q _ => sq_nonneg _)
  by_cases hB0 : B=0
  · change B ≤ ‖x‖^2
    rw [hB0]
    exact sq_nonneg _
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  have hs : (Real.sqrt B)^2=B := Real.sq_sqrt hB
  have hsp : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBp
  let a : Node → ℝ := fun q => coordinateFunctional unitTests q x/Real.sqrt B
  have ha : (∑ q ∈ Q, (a q)^2) ≤ 1 := by
    simp only [a,div_pow,← Finset.sum_div,hs]
    change B/B ≤ 1
    rw [div_self hB0]
  let g : unitTests := ⟨(Q : Set Node).indicator a,unit_antichainTest Q hQ a ha⟩
  have he : completedTestFunctional unitTests g x=Real.sqrt B := by
    rw [head_test_sum Q a (unit_antichainTest Q hQ a ha)]
    calc
      (∑ q ∈ Q, a q*coordinateFunctional unitTests q x) = B/Real.sqrt B := by
        change (∑ q ∈ Q, a q*coordinateFunctional unitTests q x) =
          (∑ q ∈ Q, (coordinateFunctional unitTests q x)^2)/Real.sqrt B
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro q hq
        dsimp only [a]
        ring
      _ = Real.sqrt B := by apply (div_eq_iff hsp.ne').mpr; nlinarith
  have hh := completedTestFunctional_abs_le unitTests g x
  rw [he,abs_of_pos hsp] at hh
  change B ≤ ‖x‖^2
  nlinarith [norm_nonneg x]

lemma coordinate_exit_segment {C : Set Node} (Q : Finset Node) (hQ : ∀ q ∈ Q, IsExit C q)
    {q r : Node} (hq : q ∈ Q) (hr : r ∈ Q) (S : Segment) (hs : S.start=r) :
    coordinateFunctional unitTests q (coreLift (segmentVector S))=if q=r then 1 else 0 := by
  rw [coordinate_coreLift,segmentVector_apply]
  by_cases he : q=r
  · have hm : q ∈ S.nodes := by rw [he,← hs]; exact S.start_mem
    rw [ite_eq_left hm,ite_eq_left he]
  · have hn : q ∉ S.nodes := by
      intro hqS
      have hh := ((S.mem_nodes q).mp hqS).1
      rw [hs] at hh
      exact (exits_incomparable (hQ r hr) (hQ q hq) (Ne.symm he)).1 hh
    simp [he,hn]

lemma coordinates_exit_mixture {I : Type*} [Fintype I] {C : Set Node}
    (Q : Finset Node) (hQ : ∀ q ∈ Q, IsExit C q) (R : I → Node → Segment)
    (hR : ∀ i q, (R i q).start=q) (p : I → ℝ) (r : I → Node → ℝ) {q : Node} (hq : q ∈ Q) :
    coordinateFunctional unitTests q (∑ i, p i • (∑ t ∈ Q, r i t • coreLift (segmentVector (R i t))))=
      ∑ i, p i*r i q := by
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have he : ∀ t ∈ Q, coordinateFunctional unitTests q (coreLift (segmentVector (R i t)))=
      if q=t then 1 else 0 := fun t ht => coordinate_exit_segment Q hQ hq ht (R i t) (hR i t)
  simp_rw [Finset.sum_congr rfl (fun t ht => congrArg (fun z : ℝ => r i t*z) (he t ht))]
  simp [hq]

lemma signed_exit_mass_sq {I : Type*} [Fintype I] {C : Set Node}
    (Q : Finset Node) (hQ : ∀ q ∈ Q, IsExit C q) (R : I → Node → Segment)
    (hR : ∀ i q, (R i q).start=q) (p : I → ℝ) (r : I → Node → ℝ) :
    (∑ q ∈ Q, (∑ i, p i*r i q)^2) ≤
      ‖∑ i, p i • (∑ q ∈ Q, r i q • coreLift (segmentVector (R i q)))‖^2 := by
  have hh := antichain_coordinates_sq Q hQ
    (∑ i, p i • (∑ q ∈ Q, r i q • coreLift (segmentVector (R i q))))
  convert hh using 1
  exact Finset.sum_congr rfl (fun q hq => by rw [coordinates_exit_mixture Q hQ R hR p r hq])

end BoundedTreePotentials.Segments

end

end OAI
