import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Cycle

namespace OAI

namespace MatchingFPRAS.Transport
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {inc : E → V → Prop}
namespace PatternCode

variable (x : PatternCode inc)

def through : Finset E := x.val.1

def closed : Finset E := x.val.2

def total : Finset E := x.through ∪ x.closed

noncomputable def ofPath (p : OddPath inc) (chord : E) (hlong : 3 ≤ p.length)
    (hc : ∀ v, inc chord v ↔ v = p.vertex 0 ∨ v = p.vertex p.length) : PatternCode inc :=
  ⟨(p.through,p.closed chord),p.closedCycle chord hlong hc,
    p.closedCycle_parity_zero chord hlong hc,p.closedCycle_parity_one chord hlong hc⟩

omit [DecidableEq V] in
lemma activated {A B : Finset E}
    (hA : MatchingOn inc A Finset.univ) (hB : MatchingOn inc B Finset.univ)
    (hT : x.through ⊆ A) (hC : x.closed ⊆ B) :
    x.total ∈ components (inc := inc) (A ∪ B) ∧
      A ∩ x.total = x.through ∧ B ∩ x.total = x.closed := by
  obtain ⟨c,ht,hc⟩ := x.property
  have heq : c.edgeSet = x.total := by
    rw [c.edgeSet_eq_parity_union,ht,hc]
    rfl
  have hU : ∀ i, c.edgeAt i ∈ A ∪ B := by
    intro i
    have he := c.edgeAt_mem_edgeSet i
    rw [heq] at he
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.mem_union_left _ (hT he)
    · exact Finset.mem_union_right _ (hC he)
  have hz : c.edgeAt 0 ∈ A := hT (by change c.edgeAt 0 ∈ x.val.1; rw [← ht]; exact c.zero_mem_parity)
  have hzn : c.edgeAt 0 ∉ B := fun hb => ((c.cycle_edge_mem_complement hA hB hU 0).mp hb) hz
  have hUr : ∀ i, c.edgeAt i ∈ B ∪ A := by simpa only [Finset.union_comm] using hU
  refine ⟨heq ▸ c.edgeSet_mem_components hA hB hU,?_,?_⟩
  · have h := c.inter_edgeSet_parity hA hB hU
    simpa only [ite_eq_left hz,heq,ht,through] using h
  · have h := c.inter_edgeSet_parity hB hA hUr
    simpa only [ite_eq_right hzn,heq,hc,closed] using h

omit [DecidableEq V] in
lemma activated_injective {A B : Finset E}
    (hA : MatchingOn inc A Finset.univ) (hB : MatchingOn inc B Finset.univ) :
    Set.InjOn (fun x : PatternCode inc => x.total)
      {x | x.through ⊆ A ∧ x.closed ⊆ B} := by
  intro x hx y hy he
  change x.total = y.total at he
  have hxx := x.activated hA hB hx.1 hx.2
  have hyy := y.activated hA hB hy.1 hy.2
  apply Subtype.ext
  apply Prod.ext
  · change x.through = y.through
    rw [← hxx.2.1,← hyy.2.1,he]
  · change x.closed = y.closed
    rw [← hxx.2.2,← hyy.2.2,he]

omit [DecidableEq V] in
lemma activated_derivative {A B : Finset E}
    (hA : MatchingOn inc A Finset.univ) (hB : MatchingOn inc B Finset.univ)
    (hT : x.through ⊆ A) (hC : x.closed ⊆ B)
    (f g : Finset E → ℝ) :
    (f ((A \ x.through) ∪ x.through) - f ((A \ x.through) ∪ x.closed)) -
      (g ((B \ x.closed) ∪ x.through) - g ((B \ x.closed) ∪ x.closed)) =
    (f A + g B) - (f (exchange A B x.total) + g (exchange B A x.total)) := by
  have hx := x.activated hA hB hT hC
  have hAT : A \ x.through = A \ x.total := by rw [← hx.2.1]; ext e; simp
  have hBC : B \ x.closed = B \ x.total := by rw [← hx.2.2]; ext e; simp
  rw [Finset.sdiff_union_of_subset hT,Finset.sdiff_union_of_subset hC,hAT,hBC]
  simp only [exchange,hx.2.1,hx.2.2]
  ring

variable [Fintype E]

noncomputable instance : Fintype (PatternCode inc) := Fintype.ofFinite _

omit [DecidableEq V] in
theorem activated_sum_le {A B : Finset E}
    (hA : MatchingOn inc A Finset.univ) (hB : MatchingOn inc B Finset.univ)
    (f g : Finset E → ℝ) :
    (∑ x : PatternCode inc, if x.through ⊆ A ∧ x.closed ⊆ B then
      ((f ((A \ x.through) ∪ x.through) - f ((A \ x.through) ∪ x.closed)) -
       (g ((B \ x.closed) ∪ x.through) - g ((B \ x.closed) ∪ x.closed)))^2 else 0)
    ≤ ∑ S ∈ components (inc := inc) (A ∪ B),
      ((f A + g B) - (f (exchange A B S) + g (exchange B A S)))^2 := by
  classical
  rw [← Finset.sum_filter]
  let active : Finset (PatternCode inc) := Finset.univ.filter (fun x => x.through ⊆ A ∧ x.closed ⊆ B)
  let cost : Finset E → ℝ := fun S =>
    ((f A + g B) - (f (exchange A B S) + g (exchange B A S)))^2
  change (∑ x ∈ active, _) ≤ ∑ S ∈ components (inc := inc) (A ∪ B), cost S
  have hinj : Set.InjOn (fun x : PatternCode inc => x.total) (active : Set (PatternCode inc)) := by
    intro x hx y hy h
    exact activated_injective hA hB (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 h
  calc
    _ = ∑ x ∈ active, cost x.total := by
      apply Finset.sum_congr rfl
      intro x hx
      have hh := (Finset.mem_filter.mp hx).2
      rw [x.activated_derivative hA hB hh.1 hh.2 f g]
    _ = ∑ S ∈ active.image (fun x => x.total), cost S := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
      intro S hS
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hS
      have hh := (Finset.mem_filter.mp hx).2
      exact (x.activated hA hB hh.1 hh.2).1) (fun S _ _ => sq_nonneg _)

end PatternCode

end MatchingFPRAS.Transport

namespace MatchingFPRAS.PairEnergy

open scoped BigOperators

structure Law (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

variable {ι Ω Δ : Type*} [Fintype ι] [Fintype Ω] [Fintype Δ]

noncomputable def guideMass (π : Law Ω) (closed : ι → Finset Ω) (X : ι) : ℝ :=
  ∑ B ∈ closed X, π.weight B

noncomputable def guideMean (π : Law Ω) (closed : ι → Finset Ω)
    (derivative : ι → Ω → ℝ) (X : ι) : ℝ :=
  (∑ B ∈ closed X, π.weight B * derivative X B) / guideMass π closed X

noncomputable def contextMass (ρ : Δ → ℝ) (arc : Δ → ι) (context : Δ → Ω)
    (X : ι) (A : Ω) : ℝ := by
  classical
  exact ∑ d with arc d = X ∧ context d = A, ρ d

noncomputable def swapSum (π : Law Ω) (through closed : ι → Finset Ω)
    (d₁ d₂ : ι → Ω → ℝ) : ℝ :=
  ∑ X, ∑ A ∈ through X, ∑ B ∈ closed X,
    π.weight A * π.weight B * (d₁ X A - d₂ X B) ^ 2

omit [Fintype Ω] in
lemma weighted_jensen (s : Finset Ω) (w b : Ω → ℝ) (a : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i) * (a - (∑ i ∈ s, w i * b i) / (∑ i ∈ s, w i)) ^ 2 ≤
      ∑ i ∈ s, w i * (a - b i) ^ 2 := by
  have hm : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  obtain hm0 | hmpos := hm.eq_or_lt
  · rw [← hm0, zero_mul]
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  · have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
        (r := fun i => w i * (a - b i))
        (f := w) (g := fun i => w i * (a - b i) ^ 2)
        hw (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
        (fun i hi => by nlinarith [sq_nonneg (w i * (a - b i))])
    have heq : (∑ i ∈ s, w i * (a - b i)) =
        (∑ i ∈ s, w i) *
          (a - (∑ i ∈ s, w i * b i) / (∑ i ∈ s, w i)) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [mul_div_cancel₀ _ (ne_of_gt hmpos)]
    rw [heq, mul_pow] at hc
    apply (mul_le_mul_iff_right₀ hmpos).mp
    nlinarith [hc]

omit [Fintype Ω] in
lemma sum_contextMass (ρ : Δ → ℝ) (arc : Δ → ι) (context : Δ → Ω)
    (through : ι → Finset Ω) (hcontext : ∀ d, context d ∈ through (arc d))
    (h : ι → Ω → ℝ) :
    (∑ d, ρ d * h (arc d) (context d)) =
      ∑ X, ∑ A ∈ through X, contextMass ρ arc context X A * h X A := by
  classical
  symm
  simp only [contextMass, Finset.sum_mul]
  calc
    _ = ∑ X, ∑ A ∈ through X,
        ∑ d with arc d = X ∧ context d = A, ρ d * h (arc d) (context d) := by
      apply Finset.sum_congr rfl
      intro X _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨hX, hA⟩ := (Finset.mem_filter.mp hd).2
      rw [hX, hA]
    _ = ∑ X, ∑ d with arc d = X, ρ d * h (arc d) (context d) := by
      apply Finset.sum_congr rfl
      intro X _
      have ht : ∀ d ∈ Finset.univ.filter (fun d => arc d = X), context d ∈ through X := by
        intro d hd
        simpa only [(Finset.mem_filter.mp hd).2] using hcontext d
      simpa only [Finset.filter_filter] using
        Finset.sum_fiberwise_of_maps_to ht (fun d => ρ d * h (arc d) (context d))
    _ = ∑ d, ρ d * h (arc d) (context d) := Finset.sum_fiberwise _ arc _

omit [Fintype ι] in
lemma tagged_context_bound {Tag : Type*} [Fintype Tag]
    (π : Law Ω) (closed : ι → Finset Ω) (ρ : Δ → ℝ)
    (arc : Δ → ι) (context guide : Δ → Ω) (tag : Δ → Tag) (C : ℝ)
    (hC : 0 ≤ C)
    (hguide : ∀ d, guide d ∈ closed (arc d))
    (hinj : Function.Injective fun d => (context d, guide d, tag d))
    (hweight : ∀ d, ρ d ≤ C * π.weight (context d) * π.weight (guide d))
    (X : ι) (A : Ω) :
    contextMass ρ arc context X A ≤
      (C * Fintype.card Tag) * π.weight A * guideMass π closed X := by
  classical
  let s : Finset Δ := Finset.univ.filter (fun d => arc d = X ∧ context d = A)
  have hmaps : ∀ d ∈ s, guide d ∈ closed X := by
    intro d hd
    have hX := (Finset.mem_filter.mp hd).2.1
    simpa only [hX] using hguide d
  have hfiber (B : Ω) : (s.filter (fun d => guide d = B)).card ≤ Fintype.card Tag := by
    apply Finset.card_le_card_of_injOn tag (t := Finset.univ)
    · intro d hd
      exact Finset.mem_univ _
    · intro d hd e he heq
      apply hinj
      have hd' := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
      have he' := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
      have hdB := (Finset.mem_filter.mp hd).2
      have heB := (Finset.mem_filter.mp he).2
      exact Prod.ext (hd'.2.trans he'.2.symm) (Prod.ext (hdB.trans heB.symm) heq)
  change (∑ d ∈ s, ρ d) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps ρ]
  calc
    _ ≤ ∑ B ∈ closed X, (Fintype.card Tag : ℝ) * (C * π.weight A * π.weight B) := by
      apply Finset.sum_le_sum
      intro B hB
      calc
        _ ≤ ∑ d ∈ s with guide d = B, C * π.weight A * π.weight B := by
          apply Finset.sum_le_sum
          intro d hd
          have hdA := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2.2
          have hdB := (Finset.mem_filter.mp hd).2
          simpa only [hdA, hdB] using hweight d
        _ = ((s.filter (fun d => guide d = B)).card : ℝ) *
            (C * π.weight A * π.weight B) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber B)
          (mul_nonneg (mul_nonneg hC (π.nonneg A)) (π.nonneg B))
    _ = _ := by
      simp only [guideMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      ring

theorem error_demand_load
    (π : Law Ω) (through closed : ι → Finset Ω) (d₁ d₂ : ι → Ω → ℝ)
    (ρ : Δ → ℝ) (arc : Δ → ι) (c₀ c₁ : Δ → Ω) (C : ℝ)
    (hρ : ∀ d, 0 ≤ ρ d) (hC : 0 ≤ C)
    (hc₀ : ∀ d, c₀ d ∈ through (arc d))
    (hc₁ : ∀ d, c₁ d ∈ through (arc d))
    (hm₀ : ∀ X A, contextMass ρ arc c₀ X A ≤ C * π.weight A * guideMass π closed X)
    (hm₁ : ∀ X A, contextMass ρ arc c₁ X A ≤ C * π.weight A * guideMass π closed X) :
    (∑ d, ρ d * (d₁ (arc d) (c₁ d) - d₁ (arc d) (c₀ d)) ^ 2) ≤
      4 * C * swapSum π through closed d₁ d₂ := by
  classical
  let μ := guideMean π closed d₂
  have hcontext (c : Δ → Ω) (hc : ∀ d, c d ∈ through (arc d))
      (hm : ∀ X A, contextMass ρ arc c X A ≤ C * π.weight A * guideMass π closed X) :
      (∑ d, ρ d * (d₁ (arc d) (c d) - μ (arc d)) ^ 2) ≤
        C * swapSum π through closed d₁ d₂ := by
    rw [sum_contextMass ρ arc c through hc (fun X A => (d₁ X A - μ X) ^ 2)]
    calc
      _ ≤ ∑ X, ∑ A ∈ through X,
          C * π.weight A * guideMass π closed X * (d₁ X A - μ X) ^ 2 := by
        apply Finset.sum_le_sum
        intro X _
        exact Finset.sum_le_sum fun A _ =>
          mul_le_mul_of_nonneg_right (hm X A) (sq_nonneg _)
      _ ≤ ∑ X, ∑ A ∈ through X, C * π.weight A *
          (∑ B ∈ closed X, π.weight B * (d₁ X A - d₂ X B) ^ 2) := by
        apply Finset.sum_le_sum
        intro X _
        apply Finset.sum_le_sum
        intro A _
        have hj := weighted_jensen (closed X) π.weight (d₂ X) (d₁ X A)
          (fun B _ => π.nonneg B)
        change guideMass π closed X * (d₁ X A - μ X) ^ 2 ≤ _ at hj
        convert mul_le_mul_of_nonneg_left hj (mul_nonneg hC (π.nonneg A)) using 1
        ring
      _ = C * swapSum π through closed d₁ d₂ := by
        simp only [swapSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro X _
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        ring
  have h₀ := hcontext c₀ hc₀ hm₀
  have h₁ := hcontext c₁ hc₁ hm₁
  calc
    _ ≤ ∑ d, (2 * (ρ d * (d₁ (arc d) (c₁ d) - μ (arc d)) ^ 2) +
          2 * (ρ d * (d₁ (arc d) (c₀ d) - μ (arc d)) ^ 2)) := by
      apply Finset.sum_le_sum
      intro d _
      nlinarith [mul_nonneg (hρ d)
        (sq_nonneg (d₁ (arc d) (c₁ d) + d₁ (arc d) (c₀ d) - 2 * μ (arc d)))]
    _ = 2 * (∑ d, ρ d * (d₁ (arc d) (c₁ d) - μ (arc d)) ^ 2) +
          2 * (∑ d, ρ d * (d₁ (arc d) (c₀ d) - μ (arc d)) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 4 * C * swapSum π through closed d₁ d₂ := by linarith

end MatchingFPRAS.PairEnergy

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

noncomputable instance instFintypePM : Fintype (PM inc) := Fintype.ofFinite _

noncomputable def gibbsLaw (w : E → ℝ) (hw : ∀ e, 0 < w e) (M : PM inc) :
    MatchingFPRAS.PairEnergy.Law (PM inc) where
  weight := gibbs w
  nonneg := fun A => le_of_lt (gibbs_pos w hw A)
  total := gibbs_sum w hw M

namespace PatternCode

noncomputable def throughStates (x : PatternCode inc) : Finset (PM inc) := by
  classical
  exact Finset.univ.filter (fun A => x.through ⊆ A.val)

noncomputable def closedStates (x : PatternCode inc) : Finset (PM inc) := by
  classical
  exact Finset.univ.filter (fun A => x.closed ⊆ A.val)

omit [DecidableEq V] in
lemma mem_throughStates (x : PatternCode inc) (A : PM inc) :
    A ∈ x.throughStates ↔ x.through ⊆ A.val := by
  classical
  simp [throughStates]

omit [DecidableEq V] in
lemma mem_closedStates (x : PatternCode inc) (A : PM inc) :
    A ∈ x.closedStates ↔ x.closed ⊆ A.val := by
  classical
  simp [closedStates]

def firstDerivative (f : Finset E → ℝ) (x : PatternCode inc) (A : PM inc) : ℝ :=
  f A.val - f ((A.val \ x.through) ∪ x.closed)

def secondDerivative (g : Finset E → ℝ) (x : PatternCode inc) (B : PM inc) : ℝ :=
  g ((B.val \ x.closed) ∪ x.through) - g B.val

end PatternCode

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

namespace ErrorDemand

variable (e : ErrorDemand hbags hG)

omit [Fintype L] in
lemma X_long : 3 ≤ (e.demand.paths.side e.X).length := by
  have hp := (e.demand.paths.side e.X).positive
  have ho := (e.demand.paths.side e.X).odd
  have hn := e.property e.X e.X_bit
  change (e.demand.paths.side e.X).length ≠ 1 at hn
  omega

noncomputable def pattern : PatternCode (BagEdge.Incident (bags := bags)) :=
  PatternCode.ofPath (e.demand.paths.side e.X) (e.demand.paths.chord e.X) e.X_long
    (e.demand.paths.chord_incidence e.X)

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

noncomputable def choice (j : Bool) : DemandEncoding BagEdge.Incident e.raw :=
  if j then e.errorOne height hheight hstep D hD w hw lo hi hlo hlohi
  else e.errorZero height hheight hstep D hD w hw lo hi hlo hlohi

lemma choice_spec (j : Bool) :
    let enc := e.choice height hheight hstep D hD w hw lo hi hlo hlohi j
    enc.first.val = e.demand.outside ∪
      (if j then e.demand.paths.contextOne e.bit e.Y else e.demand.paths.orientation e.bit) ∧
    e.pattern.closed ⊆ enc.second.val ∧
    gibbs (fun e => max lo (min hi (w e))) e.demand.1.1 *
      gibbs (fun e => max lo (min hi (w e))) e.demand.1.2 ≤
      (1000*D)^4 * gibbs (fun e => max lo (min hi (w e))) enc.first *
        gibbs (fun e => max lo (min hi (w e))) enc.second := by
  have h := (e.exists_errors height hheight hstep D hD w hw lo hi hlo hlohi).choose_spec.choose_spec
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at h
  cases j
  · exact ⟨h.1,h.2.2.1,h.2.2.2.2.1⟩
  · exact ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.2⟩

lemma choice_injective (j : Bool) : Function.Injective (fun e : ErrorDemand hbags hG =>
    (e.choice height hheight hstep D hD w hw lo hi hlo hlohi j).finiteCode) := by
  intro e f h
  exact raw_injective (DemandEncoding.finiteCode_recovers _ _ h)

lemma choice_through (j : Bool) :
    (e.choice height hheight hstep D hD w hw lo hi hlo hlohi j).first ∈ e.pattern.throughStates := by
  apply (e.pattern.mem_throughStates _).mpr
  rw [(e.choice_spec height hheight hstep D hD w hw lo hi hlo hlohi j).1]
  change (e.demand.paths.side e.X).through ⊆ _
  apply Finset.Subset.trans _ (Finset.subset_union_right)
  cases j
  · exact e.demand.paths.through_subset_orientation e.bit e.X e.X_bit
  · exact e.demand.paths.through_subset_contextOne e.bit e.X e.Y e.X_bit e.Y_bit e.X_ne_Y
      BagEdge.exists_incident

theorem context_load (M : PM (BagEdge.Incident (bags := bags))) (j : Bool)
    (X : PatternCode (BagEdge.Incident (bags := bags))) (A : PM BagEdge.Incident) :
    let wt := fun e => max lo (min hi (w e))
    let π := gibbsLaw wt (fun _ => lt_of_lt_of_le hlo (le_max_left _ _)) M
    let ρ := fun e : ErrorDemand hbags hG => gibbs wt e.demand.1.1 * gibbs wt e.demand.1.2
    let enc := fun e : ErrorDemand hbags hG => e.choice height hheight hstep D hD w hw lo hi hlo hlohi j
    MatchingFPRAS.PairEnergy.contextMass ρ pattern (fun e => (enc e).first) X A ≤
      ((1000*D)^4 * Fintype.card (DemandTag (V := V) (E := BagEdge bags))) *
        π.weight A * MatchingFPRAS.PairEnergy.guideMass π PatternCode.closedStates X := by
  dsimp only
  apply MatchingFPRAS.PairEnergy.tagged_context_bound
    (guide := fun e => (e.choice height hheight hstep D hD w hw lo hi hlo hlohi j).second)
    (tag := fun e => (e.choice height hheight hstep D hD w hw lo hi hlo hlohi j).tag)
  · positivity
  · intro e
    exact (e.pattern.mem_closedStates _).mpr
      (e.choice_spec height hheight hstep D hD w hw lo hi hlo hlohi j).2.1
  · exact choice_injective height hheight hstep D hD w hw lo hi hlo hlohi j
  · intro e
    exact (e.choice_spec height hheight hstep D hD w hw lo hi hlo hlohi j).2.2

end ErrorDemand

end MatchingFPRAS.Transport.CellDemands

end OAI
