import OAI.Combinatorics.CycleDecomposition.BatchResolution

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Batch.Splitting
open MeasureTheory ProbabilityTheory Finset Real

section BernoulliBounds
variable {Ω : Type cycleUniverse1} {I : Type cycleUniverse2} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma indicator_mem_Icc {Ω : Type cycleUniverse3} [_contextInstance1 : MeasurableSpace Ω] {X : Ω → ℝ} (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (ω : Ω) :
    X ω ∈ Set.Icc (0 : ℝ) 1 := by rcases hX ω with h | h <;> simp [h]

lemma mgf_indicator {X : Ω → ℝ} (hm : Measurable X)
    (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (p t : ℝ) (hp : ∫ ω, X ω ∂μ = p) :
    mgf X μ t = 1 + p * (exp t - 1) := by
  have hXi : Integrable X μ := Integrable.of_mem_Icc 0 1 hm.aemeasurable
    (ae_of_all _ (indicator_mem_Icc hX))
  have heq : (fun ω => exp (t * X ω)) = fun ω => (1 : ℝ) + (exp t - 1) * X ω := by
    funext ω
    rcases hX ω with h | h <;> simp [h]
  rw [mgf, heq, integral_add (integrable_const _) (hXi.const_mul _), integral_const_mul,
    hp, integral_const]
  simp [mul_comm]

lemma mgf_indicator_sum_bound {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p t : ℝ) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    mgf (∑ i ∈ s, X i) μ t ≤ exp ((s.card : ℝ) * p * (exp t - 1)) := by
  by_cases hs : s.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]
  rw [hi.mgf_sum hm]
  have heq : (∏ i ∈ s, mgf (X i) μ t) = (1 + p * (exp t - 1)) ^ s.card := by
    simp_rw [mgf_indicator (hm _) (hX _) p t (hp _)]
    simp
  rw [heq]
  have hn : 0 ≤ 1 + p * (exp t - 1) := by
    obtain ⟨i, _⟩ := hs
    rw [← mgf_indicator (hm i) (hX i) p t (hp i)]
    exact mgf_nonneg
  calc
    (1 + p * (exp t - 1)) ^ s.card ≤ exp (p * (exp t - 1)) ^ s.card :=
      pow_le_pow_left₀ hn (by linarith [add_one_le_exp (p * (exp t - 1))]) _
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma exp_neg_half_bound : exp (-(1 / 2 : ℝ)) ≤ 5 / 8 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  have hlow : (8 / 5 : ℝ) ≤ exp (1 / 2 : ℝ) := by
    nlinarith [exp_one_gt_d9, exp_pos (1 / 2 : ℝ)]
  rw [exp_neg]
  exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by norm_num at *; exact hlow)

lemma exp_half_bound : exp (1 / 2 : ℝ) ≤ 5 / 3 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  nlinarith [exp_one_lt_d9, exp_pos (1 / 2 : ℝ)]

theorem bernoulli_sum_lower_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | (∑ i ∈ s, X i ω) ≤ p * s.card / 2} ≤ exp (-p * s.card / 8) := by
  have hInt : Integrable (fun ω => exp (-(1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_le_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (p * s.card / 2)
    (by norm_num : -(1 / 2 : ℝ) ≤ 0) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(-(1 / 2 : ℝ)) * (p * s.card / 2)) *
        exp ((s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (p * s.card / 4 + (s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_neg_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

theorem bernoulli_sum_upper_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | 2 * p * s.card ≤ ∑ i ∈ s, X i ω} ≤ exp (-p * s.card / 3) := by
  have hInt : Integrable (fun ω => exp ((1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (2 * p * s.card)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(1 / 2 : ℝ) * (2 * p * s.card)) *
        exp ((s.card : ℝ) * p * (exp (1 / 2 : ℝ) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (-p * s.card + (s.card : ℝ) * p * (exp (1 / 2 : ℝ) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

end BernoulliBounds

noncomputable section
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

def CutExpansion (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ) : Prop :=
  ∀ U : Finset V, h * min (U.card : ℝ) (Uᶜ.card : ℝ) ≤
    ((P.interedges U Uᶜ).card : ℝ)

lemma boundary_sym2_injective (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges U Uᶜ : Set (V × V)) := by
  intro e he f hf hef
  rcases (Sym2.mk_eq_mk_iff.mp hef) with h | h
  · exact h
  · have he1 := (P.mem_interedges_iff.mp he).1
    have hf2 := (P.mem_interedges_iff.mp hf).2.1
    have hfirst : e.1 = f.2 := congrArg Prod.fst h
    exact False.elim ((Finset.mem_compl.mp hf2) (hfirst ▸ he1))

def edgeColorMeasure (V : Type cycleUniverse5) [Fintype V] (l : ℕ) [NeZero l] :
    Measure (Sym2 V → Fin l) :=
  Measure.pi (fun _ : Sym2 V => (PMF.uniformOfFintype (Fin l)).toMeasure)

instance edgeColorMeasure_probability (l : ℕ) [NeZero l] :
    IsProbabilityMeasure (edgeColorMeasure V l) := by
  unfold edgeColorMeasure
  infer_instance

def colorIndicator {l : ℕ} (i : Fin l) (e : Sym2 V) (ω : Sym2 V → Fin l) : ℝ :=
  if ω e = i then 1 else 0

lemma colorIndicator_indep {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {l : ℕ} [NeZero l] (i : Fin l) :
    iIndepFun (colorIndicator (V := V) i) (edgeColorMeasure V l) := by
  exact iIndepFun_pi (X := fun _ : Sym2 V => fun j : Fin l => if j = i then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

lemma colorIndicator_integral {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {l : ℕ} [NeZero l] (i : Fin l) (e : Sym2 V) :
    ∫ ω, colorIndicator i e ω ∂edgeColorMeasure V l = 1/(l : ℝ) := by
  have hl := (measurePreserving_eval
    (fun _ : Sym2 V => (PMF.uniformOfFintype (Fin l)).toMeasure) e).hasLaw
  have hi := hl.integral_comp (f := fun j : Fin l => if j = i then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  rw [PMF.integral_eq_sum] at hi
  simpa [edgeColorMeasure, colorIndicator, PMF.uniformOfFintype_apply] using hi

def colorGraph (P : SimpleGraph V) {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) :
    SimpleGraph V where
  Adj x y := P.Adj x y ∧ ω s(x,y) = i
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨by intro x h; exact P.irrefl h.1⟩

instance colorGraph_decidable (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) :
    DecidableRel (colorGraph P ω i).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

lemma colorGraph_interedges {V : Type cycleUniverse8} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) (S T : Finset V) :
    (colorGraph P ω i).interedges S T =
      (P.interedges S T).filter (fun e => ω s(e.1,e.2) = i) := by
  ext ⟨x,y⟩
  simp only [SimpleGraph.mem_interedges_iff, Finset.mem_filter]
  change (x ∈ S ∧ y ∈ T ∧ (P.Adj x y ∧ ω s(x,y) = i)) ↔ _
  tauto

lemma color_cut_sum (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) (S : Finset V) :
    (∑ e ∈ (P.interedges S Sᶜ).image (fun e => s(e.1,e.2)), colorIndicator i e ω) =
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) := by
  rw [Finset.sum_image (boundary_sym2_injective P S)]
  simp only [colorIndicator, Finset.sum_boole, colorGraph_interedges]

lemma color_cut_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] (i : Fin l) (S : Finset V) {h : ℝ}
    (hexp : CutExpansion P h) (hS : S.card ≤ Sᶜ.card) :
    (edgeColorMeasure V l).real {ω |
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} ≤
        exp (-h*S.card/(8*l)) := by
  let E := (P.interedges S Sᶜ).image (fun e => s(e.1,e.2))
  have hcard : E.card = (P.interedges S Sᶜ).card :=
    Finset.card_image_of_injOn (boundary_sym2_injective P S)
  have hl : 0 < (l : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne l)
  have hcut : h * S.card ≤ (E.card : ℝ) := by
    rw [hcard]
    have he := hexp S
    rwa [min_eq_left (by exact_mod_cast hS)] at he
  have hb := bernoulli_sum_lower_tail (μ := edgeColorMeasure V l) E
    (fun e => measurable_of_finite (colorIndicator i e)) (colorIndicator_indep i)
    (fun e ω => by simp only [colorIndicator]; split <;> simp)
    (1/(l : ℝ)) (by positivity) (colorIndicator_integral i)
  apply (measureReal_mono (show {ω |
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} ⊆
      {ω | (∑ e ∈ E, colorIndicator i e ω) ≤ (1/(l : ℝ))*E.card/2} from ?_)).trans
      (hb.trans ?_)
  · intro ω hω
    change (∑ e ∈ E, colorIndicator i e ω) ≤ (1/(l : ℝ))*E.card/2
    rw [show (∑ e ∈ E, colorIndicator i e ω) =
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) from color_cut_sum P ω i S]
    calc
      _ ≤ h*S.card/(2*l) := le_of_lt hω
      _ ≤ (E.card : ℝ)/(2*l) := div_le_div_of_nonneg_right hcut (by positivity)
      _ = _ := by ring
  · apply exp_le_exp.mpr
    have he := div_le_div_of_nonneg_right hcut (show 0 ≤ 8*(l : ℝ) by positivity)
    calc
      _ = -((E.card : ℝ)/(8*l)) := by ring
      _ ≤ -(h*S.card/(8*l)) := neg_le_neg he
      _ = _ := by ring

lemma cutExpansion_of_small_cuts (P : SimpleGraph V) [DecidableRel P.Adj] {h : ℝ}
    (hcut : ∀ S : Finset V, S.Nonempty → S.card ≤ Sᶜ.card →
      h*S.card ≤ ((P.interedges S Sᶜ).card : ℝ)) : CutExpansion P h := by
  intro S
  by_cases he : S = ∅
  · simp [he]
  by_cases hc : Sᶜ = ∅
  · simp [hc]
  by_cases hs : S.card ≤ Sᶜ.card
  · rw [min_eq_left (by exact_mod_cast hs)]
    exact hcut S (Finset.nonempty_iff_ne_empty.mpr he) hs
  · rw [min_eq_right (by exact_mod_cast le_of_not_ge hs)]
    have hi := hcut Sᶜ (Finset.nonempty_iff_ne_empty.mpr hc) (by simpa using le_of_not_ge hs)
    have hcomm : (P.interedges Sᶜ S).card = (P.interedges S Sᶜ).card := by
      have := P.symm
      exact Rel.card_interedges_comm Sᶜ S
    simpa only [compl_compl, hcomm] using hi

lemma sum_nonempty_subsets_power (q : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Finset V)).erase ∅, q^S.card) =
      (1+q)^(Fintype.card V)-1 := by
  have hs := Finset.sum_erase_add (s := Finset.univ) (fun S : Finset V => q^S.card)
    (Finset.mem_univ (∅ : Finset V))
  have hp := Finset.prod_one_add (s := (Finset.univ : Finset V)) (f := fun _ => q)
  simp only [Finset.prod_const, Finset.card_univ, Finset.powerset_univ] at hp
  simp only [Finset.card_empty, pow_zero] at hs
  linarith

theorem edge_splitting_failure_bound (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] {h : ℝ} (hexp : CutExpansion P h) :
    (edgeColorMeasure V l).real {ω | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} ≤
      l * (exp ((Fintype.card V : ℝ)*exp (-h/(8*l)))-1) := by
  let cuts : Finset (Finset V) := Finset.univ.erase ∅
  let B (i : Fin l) (S : Finset V) : Set (Sym2 V → Fin l) :=
    {ω | S.card ≤ Sᶜ.card ∧
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)}
  let q : ℝ := exp (-h/(8*l))
  have cover : {ω | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin l)), ⋃ S ∈ cuts, B i S := by
    intro ω hω
    rcases hω with ⟨i, hi⟩
    by_contra hn
    apply hi
    apply cutExpansion_of_small_cuts
    intro S hS hs
    have hb : ω ∉ B i S := by
      intro hm
      apply hn
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ _,
        Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr
          ⟨Finset.mem_erase.mpr ⟨hS.ne_empty, Finset.mem_univ _⟩, hm⟩⟩⟩⟩
    have hc : h*S.card/(2*l) ≤ (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) := by
      exact le_of_not_gt (fun hf => hb ⟨hs, hf⟩)
    convert hc using 1 ; ring
  have hbound (i : Fin l) (S : Finset V) :
      (edgeColorMeasure V l).real (B i S) ≤ q^S.card := by
    by_cases hs : S.card ≤ Sᶜ.card
    · calc
        _ ≤ (edgeColorMeasure V l).real {ω |
            (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} :=
          measureReal_mono (fun _ hw => hw.2)
        _ ≤ exp (-h*S.card/(8*l)) := color_cut_lower_tail P i S hexp hs
        _ = q^S.card := by dsimp [q]; rw [← exp_nat_mul]; congr 1; ring
    · have he : B i S = ∅ := by ext ω; simp [B,hs]
      rw [he, measureReal_empty]
      exact pow_nonneg (exp_pos _).le _
  calc
    _ ≤ (edgeColorMeasure V l).real
        (⋃ i ∈ (Finset.univ : Finset (Fin l)), ⋃ S ∈ cuts, B i S) :=
      measureReal_mono cover (measure_ne_top _ _)
    _ ≤ ∑ i : Fin l, (edgeColorMeasure V l).real (⋃ S ∈ cuts, B i S) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ i : Fin l, ∑ S ∈ cuts, (edgeColorMeasure V l).real (B i S) :=
      Finset.sum_le_sum (fun _ _ => measureReal_biUnion_finset_le _ _)
    _ ≤ ∑ _i : Fin l, ∑ S ∈ cuts, q^S.card := by
      apply Finset.sum_le_sum; intro i _; exact Finset.sum_le_sum (fun S _ => hbound i S)
    _ = (l : ℝ)*((1+q)^(Fintype.card V)-1) := by
      simp only [cuts, sum_nonempty_subsets_power, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ ≤ l*(exp ((Fintype.card V : ℝ)*q)-1) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg l)
      apply sub_le_sub_right
      calc
        _ ≤ (exp q)^(Fintype.card V) :=
          pow_le_pow_left₀ (by dsimp [q]; positivity) (by linarith [add_one_le_exp q]) _
        _ = _ := (exp_nat_mul _ _).symm

theorem edge_splitting_of_error_lt_one (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] {h : ℝ} (hexp : CutExpansion P h)
    (herror : (l : ℝ)*(exp ((Fintype.card V : ℝ)*exp (-h/(8*l)))-1) < 1) :
    ∃ ω : Sym2 V → Fin l,
      (∀ i, CutExpansion (colorGraph P ω i) (h/(2*l))) ∧
      (∀ x y, P.Adj x y ↔ ∃ i, (colorGraph P ω i).Adj x y) ∧
      (∀ i j, i ≠ j → Disjoint (colorGraph P ω i).edgeSet (colorGraph P ω j).edgeSet) := by
  have he := (edge_splitting_failure_bound P hexp).trans_lt herror
  have hh : ∃ ω : Sym2 V → Fin l, ∀ i, CutExpansion (colorGraph P ω i) (h/(2*l)) := by
    by_contra hn
    push Not at hn
    have hall : {ω : Sym2 V → Fin l | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} =
        Set.univ := Set.eq_univ_of_forall hn
    simp only [hall, Measure.real, measure_univ, ENNReal.toReal_one] at he
    exact (lt_irrefl _ he)
  obtain ⟨ω, hω⟩ := hh
  refine ⟨ω, hω, ?_, ?_⟩
  · intro x y
    exact ⟨fun hxy => ⟨ω s(x,y), hxy, rfl⟩, fun ⟨_, hxy, _⟩ => hxy⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    induction e using Sym2.ind with | _ x y =>
      have hi : (colorGraph P ω i).Adj x y := by simpa using hei
      have hj : (colorGraph P ω j).Adj x y := by simpa using hej
      exact hij (hi.2.symm.trans hj.2)

end

open Filter Asymptotics
open scoped Topology

lemma tendsto_monomial_exp_neg_power (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun D : ℝ => D^a * exp (-c * D^b)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/b) c hc).comp
    (tendsto_rpow_atTop hb)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hD.le, mul_div_cancel₀ _ hb.ne']

noncomputable def edgeSplittingScaleError (c : ℝ) (l : ℕ) (D : ℝ) : ℝ :=
  (l : ℝ) * (Real.exp (D^(51/50 : ℝ) * Real.exp ((-(c / (8*l))) * D^(9/10 : ℝ))) - 1)

lemma edgeSplittingScaleError_tendsto (c : ℝ) (hc : 0 < c) (l : ℕ) (hl : 0 < l) :
    Tendsto (edgeSplittingScaleError c l) atTop (𝓝 0) := by
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have ht := tendsto_monomial_exp_neg_power (51/50) (9/10) (c/(8*l))
    (by norm_num) (by positivity)
  have hh := ((Real.continuous_exp.tendsto 0).comp ht).sub_const 1 |>.const_mul (l : ℝ)
  unfold edgeSplittingScaleError
  convert hh using 1 <;> norm_num

universe u

theorem edge_splitting_uniform (c : ℝ) (hc : 0 < c) (l : ℕ) (hl : 0 < l) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ),
      c*D^(9/10 : ℝ) ≤ h → D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) → CutExpansion P h →
      ∃ ω : Sym2 V → Fin l,
        (∀ i, CutExpansion (colorGraph P ω i) (h/(2*l))) ∧
        (∀ x y, P.Adj x y ↔ ∃ i, (colorGraph P ω i).Adj x y) ∧
        (∀ i j, i ≠ j → Disjoint (colorGraph P ω i).edgeSet (colorGraph P ω j).edgeSet) := by
  have : NeZero l := ⟨hl.ne'⟩
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have hevent := (edgeSplittingScaleError_tendsto c hc l hl).eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨D₀,hD₀⟩ := hevent.exists_forall_of_atTop
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ h hh _hrlo hrhi hexp
  apply edge_splitting_of_error_lt_one P hexp
  apply lt_of_le_of_lt _ (hD₀ D hD)
  unfold edgeSplittingScaleError
  apply mul_le_mul_of_nonneg_left _ hlR.le
  apply sub_le_sub_right
  apply exp_le_exp.mpr
  apply mul_le_mul hrhi _ (exp_pos _).le ((Nat.cast_nonneg (Fintype.card V)).trans hrhi)
  apply exp_le_exp.mpr
  have he := div_le_div_of_nonneg_right hh (show 0 ≤ 8*(l : ℝ) by positivity)
  calc
    -h/(8*l) = -(h/(8*l)) := by ring
    _ ≤ -(c*D^(9/10 : ℝ)/(8*l)) := neg_le_neg he
    _ = -(c/(8*l))*D^(9/10 : ℝ) := by ring

end ErdosGallai.Batch.Splitting

namespace ErdosGallai.Batch
noncomputable section
open Real

def inductionPhi (x : ℝ) : ℝ :=
  if x = 1 then 1/2 else max (1/2) (1 - 1 / sqrt (logb 2 x))

lemma inductionPhi_one : inductionPhi 1 = 1/2 := by simp [inductionPhi]

lemma inductionPhi_bounds (x : ℝ) : 1/2 ≤ inductionPhi x ∧ inductionPhi x ≤ 1 := by
  by_cases hx : x = 1
  · norm_num [inductionPhi, hx]
  · simp only [inductionPhi, hx, ite_false]
    exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith [one_div_nonneg.mpr (Real.sqrt_nonneg (logb 2 x))])⟩

lemma inductionPhi_monotone : MonotoneOn inductionPhi (Set.Ici 1) := by
  intro x hx y hy hxy
  by_cases hx1 : x = 1
  · simpa [hx1, inductionPhi_one] using (inductionPhi_bounds y).1
  have hxgt : 1 < x := lt_of_le_of_ne hx (Ne.symm hx1)
  have hygt : 1 < y := hxgt.trans_le hxy
  have hlog : logb 2 x ≤ logb 2 y := Real.logb_le_logb_of_le (by norm_num)
    (by linarith) hxy
  have hxlog : 0 < logb 2 x := Real.logb_pos (by norm_num) hxgt
  have hinv := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hxlog) (Real.sqrt_le_sqrt hlog)
  simp only [inductionPhi, hx1, ne_of_gt hygt, ite_false]
  exact max_le_max le_rfl (by linarith)

lemma inductionPhi_nonconstant (x : ℝ) (hlog : 4 ≤ logb 2 x) :
    inductionPhi x = 1 - 1 / sqrt (logb 2 x) := by
  have hx : x ≠ 1 := by intro hx; subst x; norm_num at hlog
  have hsqrt : 2 ≤ sqrt (logb 2 x) := by
    convert Real.sqrt_le_sqrt hlog using 1 ; norm_num
  have hinv : 1 / sqrt (logb 2 x) ≤ 1/2 :=
    one_div_le_one_div_of_le (by norm_num) hsqrt
  simp only [inductionPhi, hx, ite_false]
  exact max_eq_right (by linarith)

def inductionDelta : ℝ := 1 / sqrt (3/10) - 1

lemma inductionDelta_pos : 0 < inductionDelta := by
  have hs : 0 < sqrt (3/10 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : sqrt (3/10 : ℝ) < 1 := by
    exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  dsimp [inductionDelta]
  have hh := (one_lt_div hs).mpr hs1
  linarith

theorem induction_potential_gain (D n : ℝ) (hD : 1 < D) (hn : D ≤ n)
    (hw : 40/3 ≤ logb 2 D) :
    inductionDelta / sqrt (logb 2 D) ≤ inductionPhi n - inductionPhi (D^(3/10:ℝ)) := by
  have hD0 : 0 < D := by linarith
  have hw0 : 0 < logb 2 D := by linarith
  have hnlog : logb 2 D ≤ logb 2 n :=
    Real.logb_le_logb_of_le (by norm_num) hD0 hn
  have hblog : logb 2 (D^(3/10:ℝ)) = (3/10)*logb 2 D := by
    exact Real.logb_rpow_eq_mul_logb_of_pos hD0
  rw [inductionPhi_nonconstant n (by linarith),
    inductionPhi_nonconstant (D^(3/10:ℝ)) (by rw [hblog]; linarith), hblog]
  have hinv := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hw0)
    (Real.sqrt_le_sqrt hnlog)
  have hid : 1 / sqrt ((3/10)*logb 2 D) - 1 / sqrt (logb 2 D) =
    inductionDelta / sqrt (logb 2 D) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3/10)]
    dsimp [inductionDelta]
    field_simp
  rw [← hid]
  linarith

lemma induction_cutoff_absorption (A w : ℝ) (hA : 0 ≤ A) (hw0 : 0 < w)
    (hw : ((A+1)/inductionDelta)^2 ≤ w) :
    (A+1)/w ≤ inductionDelta / sqrt w := by
  have hd := inductionDelta_pos
  have hratio : 0 ≤ (A+1)/inductionDelta := by positivity
  have hs : (A+1)/inductionDelta ≤ sqrt w := by
    have hh := Real.sqrt_le_sqrt hw
    simpa [Real.sqrt_sq hratio] using hh
  have hm : A+1 ≤ inductionDelta * sqrt w := by
    have := (div_le_iff₀ hd).mp hs
    simpa [mul_comm] using this
  apply (div_le_div_iff₀ hw0 (Real.sqrt_pos.mpr hw0)).mpr
  have hmul := mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg w)
  simpa [mul_assoc, Real.mul_self_sqrt hw0.le] using hmul

theorem induction_cost_absorbed (D n S C A₁ A₂ : ℝ)
    (hD : 1 < D) (hn : D ≤ n) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hA₁ : 0 ≤ A₁) (_hA₂ : 0 ≤ A₂) (hCA : 7*A₂ ≤ C)
    (hw : 40/3 ≤ logb 2 D)
    (hcut : ((A₁+1)/inductionDelta)^2 ≤ logb 2 D) :
    A₂*(S+n/logb 2 D) + (C/100)*S +
      C*inductionPhi (D^(3/10:ℝ))*(n-S/3+A₁*n/logb 2 D) ≤ C*inductionPhi n*n := by
  let f := inductionPhi (D^(3/10:ℝ))
  obtain ⟨hflo,hfhi⟩ := inductionPhi_bounds (D^(3/10:ℝ))
  have hw0 : 0 < logb 2 D := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hnw : 0 ≤ n/logb 2 D := div_nonneg hn0 hw0.le
  have hcoeff : A₂+C/100-C*f/3 ≤ 0 := by
    dsimp [f]
    nlinarith [mul_le_mul_of_nonneg_left hflo hC]
  have hScost := mul_nonpos_of_nonpos_of_nonneg hcoeff hS
  have hA₂C : A₂ ≤ C := by linarith
  have hAprod : C*f*A₁ ≤ C*A₁ := by
    exact mul_le_mul_of_nonneg_right (by
      simpa [f] using mul_le_mul_of_nonneg_left hfhi hC) hA₁
  have how := mul_le_mul_of_nonneg_right (add_le_add hA₂C hAprod) hnw
  have habs := induction_cutoff_absorption A₁ (logb 2 D) hA₁ hw0 hcut
  have hgain := induction_potential_gain D n hD hn hw
  have hpay := mul_le_mul_of_nonneg_left (habs.trans hgain) (mul_nonneg hC hn0)
  change A₂*(S+n/logb 2 D) + (C/100)*S + C*f*(n-S/3+A₁*n/logb 2 D) ≤ _
  change C*n*((A₁+1)/logb 2 D) ≤ C*n*(inductionPhi n - f) at hpay
  simp only [div_eq_mul_inv] at hScost how hpay ⊢
  nlinarith only [hScost, how, hpay]

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma cutExpansionOn_of_induce (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (h : ℝ) (he : CutExpansion (P.induce (W:Set V)) h) : CutExpansionOn P W h := by
  intro A hA
  let B : Finset (W:Set V) := univ.filter (fun x => x.val ∈ A)
  have him : B.image Subtype.val = A := by
    ext x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y,hy,rfl⟩; exact (Finset.mem_filter.mp hy).2
    · intro hx; exact ⟨⟨x,hA hx⟩,by simp [B,hx],rfl⟩
  have hcomp := subtype_image_compl W B
  rw [him] at hcomp
  have hh := he B
  rw [induced_interedges_card,him] at hh
  have hc : B.card = A.card := by rw [← him,Finset.card_image_of_injective _ Subtype.val_injective]
  have hcc : Bᶜ.card = (W \ A).card := by rw [← hcomp,Finset.card_image_of_injective _ Subtype.val_injective]
  simpa only [hc,hcc] using hh

lemma cutExpansionOn_mono {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P Q : SimpleGraph V} [DecidableRel P.Adj] [DecidableRel Q.Adj]
    {W : Finset V} {h : ℝ} (he : CutExpansionOn P W h) (hPQ : P ≤ Q) : CutExpansionOn Q W h := by
  intro A hA
  exact (he A hA).trans (Nat.cast_le.mpr (Finset.card_le_card (by
    intro e he
    simp only [SimpleGraph.mem_interedges_iff] at he ⊢
    exact ⟨he.1,he.2.1,hPQ he.2.2⟩)))

theorem uniform_two_routers_on : ∃ D₀ : ℝ, ∀ D ≥ D₀,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (R : SimpleGraph V) (W : Finset V),
    (∀ ⦃x y⦄, R.Adj x y → x ∈ W ∧ y ∈ W) →
    D^(9/10:ℝ) ≤ (W.card:ℝ) → (W.card:ℝ) ≤ D^(51/50:ℝ) →
    CutExpansionOn R W (D^(9/10:ℝ)) →
    ∃ P T : SimpleGraph V, P ≤ R ∧ T ≤ R ∧ Disjoint P.edgeSet T.edgeSet ∧
      P.edgeSet ∪ T.edgeSet = R.edgeSet ∧
      CutExpansionOn P W (D^(9/10:ℝ)/4) ∧ CutExpansionOn T W (D^(9/10:ℝ)/4) := by
  obtain ⟨D₀,hsplit⟩ := Splitting.edge_splitting_uniform 1 (by norm_num) 2 (by norm_num)
  refine ⟨D₀,?_⟩
  intro D hD V _ _ R W hW hlo hhi he
  let R' := R.induce (W:Set V)
  have he' : Splitting.CutExpansion R' (D^(9/10:ℝ)) := cutExpansion_induce R W _ he
  obtain ⟨ω,hω,hcover,hdis⟩ := hsplit D hD (W:Set V) R' (D^(9/10:ℝ))
    (by simp) (by simpa using hlo) (by simpa using hhi) he'
  let f : (W:Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let Q (i : Fin 2) := (Splitting.colorGraph R' ω i).map f
  have hQR (i : Fin 2) : Q i ≤ R := by
    apply SimpleGraph.map_le_iff_le_comap.mpr
    exact fun _ _ h => h.1
  have hind (i) : (Q i).induce (W:Set V) = Splitting.colorGraph R' ω i :=
    SimpleGraph.comap_map_eq f _
  have hexp (i) : @CutExpansionOn V _ (Q i) (fun _ _ => Classical.propDecidable _) W (D^(9/10:ℝ)/4) := by
    apply @cutExpansionOn_of_induce V _ _ (Q i) (fun _ _ => Classical.propDecidable _) W
    have hcol : CutExpansion (Splitting.colorGraph R' ω i) (D^(9/10:ℝ)/4) := by simpa only [CutExpansion, Splitting.CutExpansion, Nat.cast_ofNat, show (2:ℝ)*2=4 by norm_num] using hω i
    convert hcol using 1 ; simp only [hind]
  have hQedge (i) : (Q i).edgeSet = Sym2.map (Subtype.val : ↥(W:Set V) → V) ''
      (Splitting.colorGraph R' ω i).edgeSet := SimpleGraph.edgeSet_map f _
  refine ⟨Q 0,Q 1,hQR 0,hQR 1,?_,?_,hexp 0,hexp 1⟩
  · rw [hQedge,hQedge]
    apply Set.disjoint_left.mpr
    rintro e ⟨a,ha,hae⟩ ⟨b,hb,hbe⟩
    have hab := Sym2.map.injective Subtype.val_injective (hae.trans hbe.symm)
    subst b
    exact Set.disjoint_left.mp (hdis 0 1 (by decide)) ha hb
  · apply Set.Subset.antisymm
    · exact Set.union_subset (SimpleGraph.edgeSet_mono (hQR 0)) (SimpleGraph.edgeSet_mono (hQR 1))
    · intro e heR
      induction e using Sym2.ind with
      | _ x y =>
        have hxy : R.Adj x y := heR
        obtain ⟨i,hi⟩ := (hcover ⟨x,(hW hxy).1⟩ ⟨y,(hW hxy).2⟩).mp hxy
        have hm : s(x,y) ∈ (Q i).edgeSet := by
          rw [hQedge]
          exact ⟨s(⟨x,(hW hxy).1⟩,⟨y,(hW hxy).2⟩),hi,rfl⟩
        fin_cases i
        · exact Or.inl hm
        · exact Or.inr hm

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_adjoin_same {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hHP : ∀ j i, Disjoint (H j).edgeSet (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) := by
  let f : ∀ j, H j →g G := fun j => ⟨id,fun h => hHG j h⟩
  have he (j) : Sym2.map (f j) '' (H j).edgeSet = (H j).edgeSet := by
    have hf : (f j : V → V) = id := rfl
    rw [hf, Sym2.map_id, Set.image_id]
  apply decompositionCost_adjoin G parts hp hd (fun _ => V) H f (fun _ => Function.injective_id)
  · simpa only [he] using hHH
  · simpa only [he] using hHP
  · simpa only [he] using hu

lemma decompositionCost_assemble_same {V J : Type} [Fintype V] [Fintype J]
    (G : SimpleGraph V) (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hu : (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ ∑ j, decompositionCost (H j) := by
  simpa using decompositionCost_adjoin_same (I := Empty) G Empty.elim (fun i => nomatch i)
    (by intro i; exact i.elim) H hHG hHH (fun _ i => nomatch i) (by simpa using hu)

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

def routerRemainder {V : Type} (R : SimpleGraph V) (used : Set (Sym2 V)) : SimpleGraph V :=
  R \ SimpleGraph.fromEdgeSet used

lemma routerRemainder_edges {V : Type} (R : SimpleGraph V) (used : Set (Sym2 V)) :
    (routerRemainder R used).edgeSet = R.edgeSet \ used := by
  simp [routerRemainder,SimpleGraph.edgeSet_sdiff]

lemma routerRemainder_le {V : Type} (R : SimpleGraph V) (used : Set (Sym2 V)) :
    routerRemainder R used ≤ R := fun _ _ h => h.1

lemma protected_le_remainder {V : Type} {R T : SimpleGraph V} {used : Set (Sym2 V)}
    (hTR : T ≤ R) (htu : Disjoint T.edgeSet used) : T ≤ routerRemainder R used := by
  apply SimpleGraph.edgeSet_subset_edgeSet.mp
  rw [routerRemainder_edges]
  exact fun _ he => ⟨SimpleGraph.edgeSet_mono hTR he,fun hu => Set.disjoint_left.mp htu he hu⟩

lemma protected_avoids_used {V A : Type} (R P T : A → SimpleGraph V)
    (hRR : Pairwise fun i j => Disjoint (R i).edgeSet (R j).edgeSet)
    (hPR : ∀ i, P i ≤ R i) (hTR : ∀ i, T i ≤ R i)
    (hTP : ∀ i, Disjoint (T i).edgeSet (P i).edgeSet)
    (used : Set (Sym2 V)) (hu : used ⊆ ⋃ i, (P i).edgeSet) :
    ∀ i, Disjoint (T i).edgeSet used := by
  intro i
  apply Set.disjoint_left.mpr
  intro e he heu
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp (hu heu)
  by_cases hij : i = j
  · subst j; exact Set.disjoint_left.mp (hTP i) he hj
  · exact Set.disjoint_left.mp (hRR hij) (SimpleGraph.edgeSet_mono (hTR i) he)
      (SimpleGraph.edgeSet_mono (hPR j) hj)

lemma batch_remainder_ledger {V A K : Type} [Fintype V] [Fintype A] [Fintype K]
    (G F : SimpleGraph V) (R : A → SimpleGraph V)
    (hRG : ∀ i, R i ≤ G)
    (hRR : Pairwise fun i j => Disjoint (R i).edgeSet (R j).edgeSet)
    (hFR : ∀ i, Disjoint F.edgeSet (R i).edgeSet)
    (hcover : F.edgeSet ∪ (⋃ i, (R i).edgeSet) = G.edgeSet)
    (parts : K → Set (Sym2 V)) (hp : ∀ k, CycleOrSingleEdge G (parts k))
    (hd : Pairwise fun j k => Disjoint (parts j) (parts k))
    (used : Set (Sym2 V)) (hu : used ⊆ ⋃ i, (R i).edgeSet)
    (hparts : (⋃ k, parts k) = F.edgeSet ∪ used) :
    decompositionCost G ≤ Fintype.card K + ∑ i, decompositionCost (routerRemainder (R i) used) := by
  apply decompositionCost_adjoin_same G parts hp hd (fun i => routerRemainder (R i) used)
    (fun i => (routerRemainder_le _ _).trans (hRG i))
  · intro i j hij
    exact (hRR hij).mono (SimpleGraph.edgeSet_mono (routerRemainder_le _ _))
      (SimpleGraph.edgeSet_mono (routerRemainder_le _ _))
  · intro i k
    rw [routerRemainder_edges]
    apply Set.disjoint_left.mpr
    intro e he hp
    have hpe : e ∈ F.edgeSet ∪ used := hparts ▸ Set.mem_iUnion.mpr ⟨k,hp⟩
    rcases hpe with hpe | hpe
    · exact Set.disjoint_left.mp (hFR i) hpe he.1
    · exact he.2 hpe
  · rw [hparts,← hcover]
    simp_rw [routerRemainder_edges]
    ext e
    simp only [Set.mem_union,Set.mem_iUnion,Set.mem_sdiff]
    constructor
    · rintro ((hf | hu') | ⟨i,hi,_⟩)
      · exact Or.inl hf
      · exact Or.inr (Set.mem_iUnion.mp (hu hu'))
      · exact Or.inr ⟨i,hi⟩
    · rintro (hf | ⟨i,hi⟩)
      · exact Or.inl (Or.inl hf)
      · by_cases he : e ∈ used
        · exact Or.inl (Or.inr he)
        · exact Or.inr ⟨i,hi,he⟩

lemma prepared_quotient_cost {V I : Type} [Fintype V] [Fintype I]
    (J : SimpleGraph V) (X : I → Finset V) (hd : Pairwise fun i j => Disjoint (X i) (X j))
    (p : PreparedBatch J X hd) (W : Finset V)
    (hW : ∀ ⦃x y⦄, J.Adj x y → x ∈ W ∧ y ∈ W)
    (hX : ∀ i, X i ⊆ W) (n : ℕ) (M t : ℝ) (_ht : 0 ≤ t) (hn : W.card < n) (hM : (W.card:ℝ) ≤ M)
    (ih : ∀ (A : Type) [Fintype A] (H : SimpleGraph A), Fintype.card A < n → (Fintype.card A:ℝ) ≤ M →
      (decompositionCost H:ℝ) ≤ t * Fintype.card A) :
    ∃ k, EdgeDecomposition p.quotient k ∧
      (k:ℝ) ≤ t * ((W.card:ℝ) - ∑ i, ((X i).card / 2:ℕ)) := by
  classical
  let A := W.image (familyProject X hd p.pairing)
  let H := p.quotient.induce (A:Set (FamilyQuotient X p.pairing))
  have ho : A.card + ∑ i, (X i).card / 2 = W.card := family_quotient_image_order X hd p.pairing W hX
  have hn' : Fintype.card (A:Set (FamilyQuotient X p.pairing)) < n := by simp only [Finset.coe_sort_coe,Fintype.card_coe]; omega
  refine ⟨decompositionCost H,edgeDecomposition_on _ A (p.quotient_supported W hW) (decompositionCost_spec H),?_⟩
  have hc := ih (A:Set (FamilyQuotient X p.pairing)) H hn' (by simp only [Finset.coe_sort_coe,Fintype.card_coe]; exact (Nat.cast_le.mpr (by omega : A.card ≤ W.card)).trans hM)
  simp only [Finset.coe_sort_coe,Fintype.card_coe] at hc
  have heq : (A.card:ℝ) = (W.card:ℝ) - ∑ i, ((X i).card / 2:ℕ) := by
    have hh : (A.card:ℝ) + ∑ i, ((X i).card / 2:ℕ) = W.card := by exact_mod_cast ho
    linarith
  rwa [heq] at hc

end
end ErdosGallai.Batch

namespace ErdosGallai.Batch
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

theorem uniform_coupled_resolution_cost : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
    ∀ (V A B : Type) [Fintype V] [Fintype A] [Fintype B],
    ∀ (G F : SimpleGraph V) (R : A → SimpleGraph V) (U : A → Finset V),
    F ≤ G → (∀ r, R r ≤ G) →
    Pairwise (fun r s => Disjoint (R r).edgeSet (R s).edgeSet) →
    Pairwise (fun r s => Disjoint (U r) (U s)) →
    (∀ r, ∀ ⦃x y⦄, (R r).Adj x y → x ∈ U r ∧ y ∈ U r) →
    (∀ r, Disjoint F.edgeSet (R r).edgeSet) →
    F.edgeSet ∪ (⋃ r, (R r).edgeSet) = G.edgeSet →
    (∀ r, CutExpansionOn (R r) (U r) (D^(9/10:ℝ))) →
    (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
    ∀ (J : B → SimpleGraph V) (W : B → Finset V),
    (∀ b, J b ≤ F) → Pairwise (fun b c => Disjoint (J b).edgeSet (J c).edgeSet) →
    (⋃ b, (J b).edgeSet) = F.edgeSet →
    (∀ b, ∀ ⦃x y⦄, (J b).Adj x y → x ∈ W b ∧ y ∈ W b) →
    (∀ b, ((W b).card:ℝ) ≤ D^(3/10:ℝ)) →
    ∀ (I : B → Type) [∀ b, Fintype (I b)] (X : ∀ b, I b → Finset V)
      (_hXd : ∀ b, Pairwise fun i j => Disjoint (X b i) (X b j)),
    (∀ b i, X b i ⊆ W b) →
    ∀ rX : ∀ b, I b → A,
    (∀ b i, X b i ⊆ U (rX b i)) →
    (∀ b i v, v ∈ X b i → (F.degree v:ℝ) ≤ D^(1/100:ℝ)) →
    1 ≤ D^(1/100:ℝ) → (∀ b i, 8 ≤ (X b i).card) →
    (∀ b i, (D^(1/100:ℝ))^2 ≤ (X b i).card) →
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → (∀ b, (W b).card < n) →
    (∀ (Q : Type) [Fintype Q] (H : SimpleGraph Q), Fintype.card Q < n →
      (Fintype.card Q:ℝ) ≤ D^(3/10:ℝ) → (decompositionCost H:ℝ) ≤ t * Fintype.card Q) →
    ∃ H : A → SimpleGraph V,
      (∀ r, H r ≤ R r) ∧
      (∀ r, CutExpansionOn (H r) (U r) (D^(9/10:ℝ)/4)) ∧
      (decompositionCost G:ℝ) ≤
        t * ((∑ b, ((W b).card:ℝ)) - ∑ b, ∑ i, ((X b i).card / 2:ℕ)) +
        8 * (∑ b, ∑ i, ((X b i).card:ℝ)) + ∑ r, (decompositionCost (H r):ℝ) := by
  obtain ⟨D₁,hsplit⟩ := uniform_two_routers_on
  obtain ⟨D₂,hD₂,hresolve⟩ := uniform_batch_resolution
  refine ⟨max D₁ D₂,lt_of_lt_of_le hD₂ (le_max_right _ _),?_⟩
  intro D hD V A B _ _ _ G F R U hFG hRG hRR hUU hRU hFR hcover he hr
    J W hJF hJJ hJu hW hWnum I _ X hXd hXW rX hXU hdeg ha hm hma n t ht hn ih
  have hs (r : A) := hsplit D ((le_max_left _ _).trans hD) V (R r) (U r)
    (hRU r) (hr r).1 (hr r).2 (he r)
  choose P T hPR hTR hPT hPu hPe hTe using hs
  have hPP : Pairwise fun r s => Disjoint (P r).edgeSet (P s).edgeSet :=
    fun _ _ h => (hRR h).mono (SimpleGraph.edgeSet_mono (hPR _)) (SimpleGraph.edgeSet_mono (hPR _))
  have hp (b : B) : Nonempty (PreparedBatch (J b) (X b) (hXd b)) :=
    prepare_batch (J b) (X b) (hXd b) (D^(1/100:ℝ)) ha (hm b) (hma b)
      (fun i v hv => (Nat.cast_le.mpr (SimpleGraph.degree_le_of_le (hJF b))).trans (hdeg b i v hv))
  let prep (b : B) := Classical.choice (hp b)
  have hq (b : B) := prepared_quotient_cost (J b) (X b) (hXd b) (prep b) (W b)
    (hW b) (hXW b) n (D^(3/10:ℝ)) t ht (hn b) (hWnum b) ih
  choose k hk hkc using hq
  obtain ⟨K,hK,parts,used,hcount,hparts,hdis,hused,hFu,hpartscover⟩ :=
    hresolve D ((le_max_right _ _).trans hD) V A B G F P U hFG
      (fun r => (hPR r).trans (hRG r)) hPP hUU
      (fun r => (hFR r).mono_right (SimpleGraph.edgeSet_mono (hPR r))) hPe hr
      J W hJF hJJ hJu hW hWnum I X hXd hXW rX hXU hdeg prep k hk
  let : Fintype K := hK
  have husedR : used ⊆ ⋃ r, (R r).edgeSet := hused.trans (Set.iUnion_mono fun r => SimpleGraph.edgeSet_mono (hPR r))
  have hTu := protected_avoids_used R P T hRR hPR hTR (fun r => (hPT r).symm) used hused
  let H (r : A) := routerRemainder (R r) used
  have hcost := batch_remainder_ledger G F R hRG hRR hFR hcover parts hparts hdis used husedR hpartscover
  refine ⟨H,fun r => routerRemainder_le _ _,fun r => ?_,?_⟩
  · exact cutExpansionOn_mono (hTe r) (protected_le_remainder (hTR r) (hTu r))
  · have hkreal : (Fintype.card K:ℝ) ≤ (∑ b, (k b:ℝ)) + 8 * (∑ b, ∑ i, ((X b i).card:ℝ)) := by
      exact_mod_cast hcount
    have hqsum := Finset.sum_le_sum (s := univ) (fun b _ => hkc b)
    have hqsum' : (∑ b, (k b:ℝ)) ≤
        t * ((∑ b, ((W b).card:ℝ)) - ∑ b, ∑ i, ((X b i).card / 2:ℕ)) := by
      simpa only [Finset.mul_sum,Finset.sum_sub_distrib,mul_sub,Nat.cast_sum] using hqsum
    have hc : (decompositionCost G:ℝ) ≤ (Fintype.card K:ℝ) + ∑ r, (decompositionCost (H r):ℝ) := by
      exact_mod_cast hcost
    linarith

end
end ErdosGallai.Batch

end
end
end

end OAI
