import OAI.Probability.GammaPassage.GoodSiteBlocks
import OAI.Probability.GammaPassage.SourceConnector

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def trialOffset (M : ℕ) (R s : ℝ) (j : Fin M) : ℝ :=
  (2*((j.val : ℝ)+1)-(M : ℝ)-1)*3*trialSpacing R s

noncomputable def trialTranslate (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j : Fin M) : Vertex :=
  (X,⌊b*X+Y+trialOffset M R s j+1/2⌋)

theorem nearest_integer_error (t : ℝ) : |(⌊t+1/2⌋ : ℝ)-t| ≤ 1/2 := by
  have hlo := Int.floor_le (t+1/2)
  have hhi := Int.lt_floor_add_one (t+1/2)
  apply abs_le.mpr
  constructor <;> linarith

theorem trialTranslate_error (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j : Fin M) :
    |transverse b (trialTranslate b X Y M R s j)-(Y+trialOffset M R s j)| ≤ 1/2 := by
  have hh := nearest_integer_error (b*X+Y+trialOffset M R s j)
  convert hh using 1
  simp [trialTranslate,transverse]
  congr 1
  ring

theorem trialSpacing_bounds (R s : ℝ) (hR : 0 ≤ R) (hs : 1 ≤ s) :
    1 ≤ trialSpacing R s ∧ R*s ≤ trialSpacing R s := by
  have hc := Nat.le_ceil s
  have hn : (1 : ℝ) ≤ (⌈s⌉₊ : ℝ) := by linarith
  unfold trialSpacing
  constructor
  · nlinarith
  · nlinarith

theorem trialOffset_bound (M : ℕ) (R s : ℝ) (j : Fin M)
    (hR : 0 ≤ R) (hs : 1 ≤ s) :
    |trialOffset M R s j| ≤ 3*M*trialSpacing R s := by
  have hB := (trialSpacing_bounds R s hR hs).1
  have hj : (j.val : ℝ)+1 ≤ M := by exact_mod_cast j.isLt
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have ha : |2*((j.val : ℝ)+1)-(M : ℝ)-1| ≤ M := by
    apply abs_le.mpr
    constructor <;> linarith
  unfold trialOffset
  rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<3),abs_of_nonneg (show 0 ≤ trialSpacing R s by linarith)]
  nlinarith

/-- Every translated strip of half-width `R*s` lies inside its `S₀/4`
window, including the half-unit lattice-phase error. -/
theorem trial_strip_in_window (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j : Fin M) (hR : 0 ≤ R) (hs : 1 ≤ s)
    (p : Vertex) (hp : |transverse b p-transverse b (trialTranslate b X Y M R s j)| ≤ R*s) :
    |transverse b p-Y| ≤ trialWindow M R s/4 := by
  have he := trialTranslate_error b X Y M R s j
  have ho := trialOffset_bound M R s j hR hs
  have hB := trialSpacing_bounds R s hR hs
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast j.pos
  have hh := abs_add_le
    (transverse b (trialTranslate b X Y M R s j)-(Y+trialOffset M R s j))
    (trialOffset M R s j)
  have heq : transverse b (trialTranslate b X Y M R s j)-(Y+trialOffset M R s j)+
      trialOffset M R s j = transverse b (trialTranslate b X Y M R s j)-Y := by ring
  rw [heq] at hh
  have ht := abs_add_le (transverse b p-transverse b (trialTranslate b X Y M R s j))
    (transverse b (trialTranslate b X Y M R s j)-Y)
  rw [sub_add_sub_cancel] at ht
  unfold trialWindow
  nlinarith [mul_le_mul_of_nonneg_right hM (by linarith : 0 ≤ trialSpacing R s)]

/-- Distinct trials have strictly disjoint transverse strips, uniformly in
both the longitudinal column and the real transverse phase. -/
theorem trial_centers_separated (b : ℝ) (X : ℤ) (Y : ℝ)
    (M : ℕ) (R s : ℝ) (j l : Fin M) (hjl : j ≠ l) (hR : 0 ≤ R) (hs : 1 ≤ s) :
    2*R*s < |transverse b (trialTranslate b X Y M R s j)-
      transverse b (trialTranslate b X Y M R s l)| := by
  have hB := trialSpacing_bounds R s hR hs
  have he := trialTranslate_error b X Y M R s j
  have hf := trialTranslate_error b X Y M R s l
  have he' := abs_le.mp he
  have hf' := abs_le.mp hf
  have hdiff : trialOffset M R s j-trialOffset M R s l =
      6*((j.val : ℝ)-(l.val : ℝ))*trialSpacing R s := by unfold trialOffset; ring
  have hne : j.val ≠ l.val := fun hh => hjl (Fin.ext hh)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hn : (j.val : ℝ)+1 ≤ l.val := by exact_mod_cast hlt
    have ha := neg_le_abs (transverse b (trialTranslate b X Y M R s j)-
      transverse b (trialTranslate b X Y M R s l))
    nlinarith [mul_le_mul_of_nonneg_right hn (by linarith : 0 ≤ trialSpacing R s)]
  · have hn : (l.val : ℝ)+1 ≤ j.val := by exact_mod_cast hgt
    have ha := le_abs_self (transverse b (trialTranslate b X Y M R s j)-
      transverse b (trialTranslate b X Y M R s l))
    nlinarith [mul_le_mul_of_nonneg_right hn (by linarith : 0 ≤ trialSpacing R s)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
variable {shape rate : ℝ}

theorem rareFastTrials_disjoint (b A R s : ℝ) (n X : ℤ) (Y : ℝ) (M : ℕ)
    (hR : 0 ≤ R) (hs : 1 ≤ s) :
    Pairwise (fun j l : Fin M => Disjoint
      (rareFastVertices b A R s n (trialTranslate b X Y M R s j))
      (rareFastVertices b A R s n (trialTranslate b X Y M R s l))) := by
  intro j l hjl
  apply strip_vertices_disjoint _ _ b
    (transverse b (trialTranslate b X Y M R s j))
    (transverse b (trialTranslate b X Y M R s l)) (R*s)
  · intro p hp
    have hh := ((mem_rareFastVertices ..).mp hp).2.2
    convert hh using 1
    simp [transverse]
    congr 1
    ring
  · intro p hp
    have hh := ((mem_rareFastVertices ..).mp hp).2.2
    convert hh using 1
    simp [transverse]
    congr 1
    ring
  · simpa only [mul_assoc] using trial_centers_separated b X Y M R s j l hjl hR hs

/-- Disjoint translated trials amplify the original crossing success
probability. -/
theorem rareFastTrials_failure_bound (h : GammaEnvironment shape rate P τ)
    (b m a A R ε s p0 : ℝ) (n X : ℤ) (Y : ℝ) (M : ℕ)
    (hR : 0 ≤ R) (hs : 1 ≤ s)
    (hp0 : p0 ≤ P.real {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n 0}) :
    P.real {ω | ∀ j : Fin M, (fun e => τ e ω) ∉ rareFastEvent b m a A R ε s n
      (trialTranslate b X Y M R s j)} ≤ (1-p0)^M := by
  have hh := Grid.disjoint_trials_failure_bound h (Finset.univ : Finset (Fin M))
    (fun j => rareFastEvent b m a A R ε s n (trialTranslate b X Y M R s j))
    (fun j => internalEdges (rareFastVertices b A R s n (trialTranslate b X Y M R s j)))
    (fun _ _ => measurableSet_rareFastEvent ..) (fun j _ => rareFastEvent_depends b m a A R ε s n (trialTranslate b X Y M R s j))
    (fun _ _ _ _ hij => internalEdges_disjoint (rareFastTrials_disjoint b A R s n X Y M hR hs hij))
    p0 (fun j _ => ?_)
  · simpa using hh
  · unfold Measure.real
    rw [rareFastEvent_probability_translate h]
    exact hp0

end GammaFPP.CrossingBridge

end OAI
