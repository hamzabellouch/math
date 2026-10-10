import OAI.Analysis.TreePotential.StartPolar

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.Segments

/-- Start masses indexed by the literal (component,prefix) array. There is one
entry per actual segment, not one entry per path or per chain. -/
def startArray (w : Segment → ℝ≥0∞) (n : ℕ) (s : List ℕ) : ℝ≥0∞ :=
  ∑' S : Segment, if n=S.start.1 ∧ s=S.start.2.val then w S else 0

lemma startArray_mono {w z : Segment → ℝ≥0∞} (h : w ≤ z) : startArray w ≤ startArray z := by
  intro n s
  apply ENNReal.tsum_le_tsum
  intro S
  split_ifs
  · exact h S
  · rfl

lemma startArray_add (w z : Segment → ℝ≥0∞) : startArray (w+z)=startArray w+startArray z := by
  funext n s
  change (∑' S : Segment,if n=S.start.1 ∧ s=S.start.2.val then w S+z S else 0)=_
  have he (S : Segment) : (if n=S.start.1 ∧ s=S.start.2.val then w S+z S else 0)=
      (if n=S.start.1 ∧ s=S.start.2.val then w S else 0)+(if n=S.start.1 ∧ s=S.start.2.val then z S else 0) := by
    split_ifs <;> simp
  simp_rw [he]
  exact ENNReal.tsum_add

lemma startArray_mul (a : ℝ≥0∞) (w : Segment → ℝ≥0∞) :
    startArray (fun S => a*w S)=fun n s => a*startArray w n s := by
  funext n s
  simp only [startArray,← ENNReal.tsum_mul_left,mul_ite,mul_zero]

lemma startArray_tsum {I : Type*} (w : I → Segment → ℝ≥0∞) :
    startArray (fun S => ∑' i,w i S)=fun n s => ∑' i,startArray (w i) n s := by
  funext n s
  simp only [startArray]
  have he (S : Segment) : (if n=S.start.1 ∧ s=S.start.2.val then ∑' i,w i S else 0)=
      ∑' i,if n=S.start.1 ∧ s=S.start.2.val then w i S else 0 := by
    split_ifs <;> simp
  simp_rw [he]
  exact ENNReal.tsum_comm

@[simp] lemma startArray_zero : startArray 0=0 := by funext n s; simp [startArray]

lemma forest_treeSum_startArray (w : Segment → ℝ≥0∞) (b : (n : ℕ) → List ℕ → ℝ≥0∞) :
    (∑' n : ℕ,treeSum (n+1) (fun s => startArray w n s*b n s))=
      ∑' S : Segment,w S*b S.start.1 S.start.2.val := by
  have he (n : ℕ) (s : List ℕ) : startArray w n s*b n s=
      ∑' S : Segment,if n=S.start.1 then (if s=S.start.2.val then w S*b S.start.1 S.start.2.val else 0) else 0 := by
    rw [startArray,← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro S
    by_cases hn : n=S.start.1
    · subst n
      by_cases hs : s=S.start.2.val
      · subst s
        simp
      · simp [hs]
    · simp [hn]
  simp_rw [he,treeSum_tsum]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro S
  have he' (n : ℕ) : treeSum (n+1) (fun s => if n=S.start.1 then (if s=S.start.2.val then w S*b S.start.1 S.start.2.val else 0) else 0)=
      if n=S.start.1 then w S*b S.start.1 S.start.2.val else 0 := by
    by_cases hn : n=S.start.1
    · subst n
      simp only [ite_true]
      exact treeSum_single _ _ S.start.2.property _
    · simp only [hn,ite_false]
      exact treeSum_zero _
  simp_rw [he']
  simp

lemma representation_test_energy (a : Segment → ℝ) (g : Node → ℝ) (hg : IsUnitTest g) :
    (∑' S : Segment,ENNReal.ofReal |a S*S.eval g|) ≤
      forestCost (startArray (fun S => ENNReal.ofReal |a S|)) := by
  calc
    _ = ∑' S : Segment,ENNReal.ofReal |a S| *ENNReal.ofReal |S.eval g| := by
      apply tsum_congr
      intro S
      rw [abs_mul,ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ ∑' S : Segment,ENNReal.ofReal |a S| *coneBudget g S.start.1 S.start.2.val := by
      apply ENNReal.tsum_le_tsum
      intro S
      exact mul_le_mul le_rfl (segment_le_coneBudget g S) zero_le zero_le
    _ = ∑' n : ℕ,treeSum (n+1) (fun s => startArray (fun S => ENNReal.ofReal |a S|) n s*coneBudget g n s) :=
      (forest_treeSum_startArray _ _).symm
    _ ≤ _ := forest_pair_budget_le _ g hg

/-- The start cost of a signed segment representation. -/
def representationCost (a : Segment → ℝ) : ℝ≥0∞ :=
  forestCost (startArray (fun S => ENNReal.ofReal |a S|))

lemma representationCost_add (a b : Segment → ℝ) : representationCost (a+b) ≤ representationCost a+representationCost b := by
  calc
    _ ≤ forestCost (startArray ((fun S => ENNReal.ofReal |a S|)+(fun S => ENNReal.ofReal |b S|))) := by
      apply forestCost_mono
      apply startArray_mono
      intro S
      change ENNReal.ofReal |a S+b S| ≤ ENNReal.ofReal |a S|+ENNReal.ofReal |b S|
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = _ := by rw [startArray_add]
    _ ≤ _ := forestCost_add _ _

lemma representationCost_smul (c : ℝ) (a : Segment → ℝ) :
    representationCost (c • a)=ENNReal.ofReal |c| *representationCost a := by
  unfold representationCost
  simp only [Pi.smul_apply,smul_eq_mul,abs_mul,ENNReal.ofReal_mul (abs_nonneg _),startArray_mul,forestCost_mul]

@[simp] lemma representationCost_zero : representationCost 0=0 := by
  unfold representationCost
  simp only [Pi.zero_apply,abs_zero,ENNReal.ofReal_zero]
  change forestCost (startArray 0)=0
  rw [startArray_zero]
  change eTwo (fun n : ℕ => startCost (n+1) 0)=0
  simp only [startCost_zero]
  exact eTwo_zero ℕ

lemma startArray_nonzero {w : Segment → ℝ≥0∞} {n : ℕ} {s : List ℕ}
    (h : startArray w n s≠0) : ∃ S : Segment,n=S.start.1 ∧ s=S.start.2.val ∧ w S≠0 := by
  by_contra hn
  apply h
  apply ENNReal.tsum_eq_zero.mpr
  intro S
  by_cases hs : n=S.start.1 ∧ s=S.start.2.val
  · have hz : w S=0 := by
      by_contra hw
      exact hn ⟨S,hs.1,hs.2,hw⟩
    simp [hs,hz]
  · simp [hs]

def Atom.representation (A : Atom) : Segment → ℝ := (A.family : Set Segment).indicator A.coeff

lemma Atom.representation_apply (A : Atom) (S : Segment) :
    A.representation S=if S ∈ A.family then A.coeff S else 0 := by
  simp only [Atom.representation,Set.indicator_apply,Finset.mem_coe]

lemma Atom.start_injective (A : Atom) : Set.InjOn Segment.start (A.family : Set Segment) := by
  intro S hS T hT he
  by_contra hne
  exact (A.incomparable S hS T hT hne).1 (he ▸ prefix_refl _)

lemma Atom.mass_antichain (A : Atom) (n : ℕ) :
    AntichainMass (n+1) (startArray (fun S => ENNReal.ofReal |A.representation S|) n) := by
  intro s t hs ht hms hmt hst
  obtain ⟨S,hSn,hsS,hS⟩ := startArray_nonzero hms
  obtain ⟨T,hTn,htT,hT⟩ := startArray_nonzero hmt
  have hSA : S ∈ A.family := by
    by_contra hh
    simp [Atom.representation_apply,hh] at hS
  have hTA : T ∈ A.family := by
    by_contra hh
    simp [Atom.representation_apply,hh] at hT
  have hST : Prefix S.start T.start := ⟨hSn.symm.trans hTn,hsS ▸ htT ▸ hst⟩
  have he : S=T := by
    by_contra hne
    exact (A.incomparable S hSA T hTA hne).1 hST
  exact hsS.trans (he ▸ htT.symm)

lemma Atom.mass_at_start (A : Atom) {S : Segment} (hS : S ∈ A.family) :
    startArray (fun T => ENNReal.ofReal |A.representation T|) S.start.1 S.start.2.val=
      ENNReal.ofReal |A.coeff S| := by
  rw [startArray,tsum_eq_single S]
  · simp [Atom.representation_apply,hS]
  · intro T hTS
    by_cases hT : T ∈ A.family
    · have hstart : T.start ≠ S.start := fun he => hTS (A.start_injective hT hS he)
      have hn : ¬(S.start.1=T.start.1 ∧ S.start.2.val=T.start.2.val) := by
        rintro ⟨hc,hl⟩
        apply hstart
        rcases S with ⟨⟨n,s⟩,v,hv⟩
        rcases T with ⟨⟨m,t⟩,w,hw⟩
        dsimp at hc hl ⊢
        subst m
        have hst : s=t := Subtype.ext hl
        subst t
        rfl
      simp [hn]
    · simp [Atom.representation_apply,hT]

lemma Atom.representation_cost (A : Atom) : representationCost A.representation ≤ 1 := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ)<2)).mp
  simp only [ENNReal.rpow_two,one_pow]
  unfold representationCost
  rw [forestCost_antichain_sq _ A.mass_antichain]
  have he : (∑' n : ℕ,treeSum (n+1) (fun s => (startArray (fun S => ENNReal.ofReal |A.representation S|) n s)^2))=
      ∑' S : Segment,(ENNReal.ofReal |A.representation S|)^2 := by
    simp only [sq]
    rw [forest_treeSum_startArray]
    apply tsum_congr
    intro S
    by_cases hS : S ∈ A.family
    · rw [A.mass_at_start hS,Atom.representation_apply,ite_eq_left hS]
    · simp [Atom.representation_apply,hS]
  rw [he]
  have he' : (∑' S : Segment,(ENNReal.ofReal |A.representation S|)^2)=
      ENNReal.ofReal (∑ S ∈ A.family,(A.coeff S)^2) := by
    rw [tsum_eq_sum (s:=A.family)]
    · rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      apply Finset.sum_congr rfl
      intro S hS
      rw [Atom.representation_apply,ite_eq_left hS,← ENNReal.ofReal_pow (abs_nonneg _),sq_abs]
    · intro S hS
      simp [Atom.representation_apply,hS]
  rw [he']
  simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal A.budget

lemma representation_finite_energy (a : Segment → ℝ) (g : Node →₀ ℝ) :
    (∑' S : Segment,ENNReal.ofReal |a S*S.eval g|) ≤
      representationCost a*ENNReal.ofReal (testNorm atomTests g) := by
  let R := testNorm atomTests g
  have hR : 0 ≤ R := testNorm_nonneg _ _
  by_cases hz : R=0
  · have hg : g=0 := (testNorm_eq_zero atomTests g).mp hz
    subst g
    simp only [Finsupp.coe_zero,Segment.eval_zero,mul_zero,abs_zero,ENNReal.ofReal_zero,tsum_zero,
      testNorm_zero,mul_zero]
    exact le_rfl
  · have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
    let f : Node →₀ ℝ := R⁻¹ • g
    have hf : IsUnitTest f := by
      apply (predual_unit_iff f).mp
      change testNorm atomTests (R⁻¹ • g) ≤ 1
      change (testSeminorm atomTests) (R⁻¹ • g) ≤ 1
      rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
      change R⁻¹*R≤1
      simp [hz]
    have he (S : Segment) : S.eval g=R*S.eval f := by
      change S.eval g=R*S.eval (R⁻¹ • g)
      rw [Segment.eval_smul,← mul_assoc,mul_inv_cancel₀ hz,one_mul]
    have he' (S : Segment) : ENNReal.ofReal |a S*S.eval g|=
        ENNReal.ofReal |a S*S.eval f| *ENNReal.ofReal R := by
      rw [he S]
      have hh : a S*(R*S.eval f)=(a S*S.eval f)*R := by ring
      rw [hh,abs_mul,abs_of_pos hp,ENNReal.ofReal_mul (abs_nonneg _)]
    simp_rw [he']
    rw [ENNReal.tsum_mul_right]
    exact mul_le_mul (representation_test_energy a f hf) le_rfl zero_le zero_le

lemma real_series_bound {I : Type*} (f : I → ℝ) {C : ℝ≥0∞} (hC : C≠∞)
    (h : (∑' i,ENNReal.ofReal |f i|) ≤ C) : Summable f ∧ |∑' i,f i| ≤ C.toReal := by
  have ht : (∑' i,ENNReal.ofReal |f i|)≠∞ := ne_top_of_le_ne_top hC h
  have habs : Summable (fun i => |f i|) := by
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using ENNReal.summable_toReal ht
  have hs : Summable f := Summable.of_norm (by simpa only [Real.norm_eq_abs] using habs)
  refine ⟨hs,?_⟩
  have hh := norm_tsum_le_tsum_norm (show Summable (fun i => ‖f i‖) by simpa only [Real.norm_eq_abs] using habs)
  simp only [Real.norm_eq_abs] at hh
  have he : (∑' i,|f i|)=(∑' i,ENNReal.ofReal |f i|).toReal := by
    rw [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (abs_nonneg _)]
  exact hh.trans (he ▸ ENNReal.toReal_mono hC h)

lemma representation_series_bound (a : Segment → ℝ) (ha : representationCost a≠∞) (g : Node →₀ ℝ) :
    Summable (fun S => a S*S.eval g) ∧
      |∑' S : Segment,a S*S.eval g| ≤ (representationCost a).toReal*testNorm atomTests g := by
  have hC : representationCost a*ENNReal.ofReal (testNorm atomTests g)≠∞ := ENNReal.mul_ne_top ha ENNReal.ofReal_ne_top
  have hh := real_series_bound (fun S : Segment => a S*S.eval g) hC (representation_finite_energy a g)
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (testNorm_nonneg atomTests g)] using hh

/-- The absolutely convergent countable representation pairing on finitely supported tests. -/

def representationPairing (a : Segment → ℝ) (ha : representationCost a≠∞) : (Node →₀ ℝ) →ₗ[ℝ] ℝ where
  toFun g := ∑' S : Segment,a S*S.eval g
  map_add' g h := by
    have h1 := (representation_series_bound a ha g).1
    have h2 := (representation_series_bound a ha h).1
    simpa only [Finsupp.coe_add,Segment.eval_add,mul_add] using h1.tsum_add h2
  map_smul' c g := by
    change (∑' S : Segment,a S*S.eval (c • g))=c*(∑' S : Segment,a S*S.eval g)
    simp only [Segment.eval_smul]
    simp_rw [show ∀ S : Segment,a S*(c*S.eval g)=c*(a S*S.eval g) by intro S; ring]
    rw [tsum_mul_left]

end BoundedTreePotentials.Segments

end

end OAI
