import Mathlib

namespace OAI

section

namespace PlanarL1.Clipping

open scoped NNReal

variable {X : Type*} [PseudoMetricSpace X]

/-- The literal capped frontier extension; the empty frontier contributes
+infinity before taking the minimum, so the finite result is the cap. -/
noncomputable def envelope (S : Set X) (s : X → ℝ) (cap t : ℝ) (x : X) : ℝ := by
  classical
  exact if S.Nonempty then min cap (sInf ((fun z => s z+t*dist x z) '' S)) else cap

lemma envelope_le_cap (S : Set X) (s : X → ℝ) (cap t : ℝ) (x : X) :
    envelope S s cap t x ≤ cap := by
  classical
  unfold envelope
  split
  · exact min_le_left _ _
  · rfl

lemma cost_continuousOn {S : Set X} {s : X → ℝ} (hs : ContinuousOn s S) (t : ℝ) (x : X) :
    ContinuousOn (fun z => s z+t*dist x z) S :=
  hs.add (continuous_const.mul (continuous_const.dist continuous_id)).continuousOn

lemma inf_attained {S : Set X} {s : X → ℝ} (hS : IsCompact S) (hs : ContinuousOn s S)
    (hne : S.Nonempty) (t : ℝ) (x : X) :
    ∃ z ∈ S, sInf ((fun z => s z+t*dist x z) '' S) = s z+t*dist x z := by
  obtain ⟨z,hz,hmin⟩ := hS.exists_isMinOn hne (cost_continuousOn hs t x)
  refine ⟨z,hz,le_antisymm ?_ ?_⟩
  · exact csInf_le (hS.image_of_continuousOn (cost_continuousOn hs t x)).bddBelow
      ⟨z,hz,rfl⟩
  · apply le_csInf (hne.image _)
    rintro _ ⟨y,hy,rfl⟩
    exact hmin hy

lemma envelope_le_cost {S : Set X} {s : X → ℝ} (hS : IsCompact S) (hs : ContinuousOn s S)
    (cap t : ℝ) (x : X) {z : X} (hz : z ∈ S) :
    envelope S s cap t x ≤ s z+t*dist x z := by
  classical
  rw [envelope,ite_eq_left ⟨z,hz⟩]
  exact (min_le_right _ _).trans (csInf_le
    (hS.image_of_continuousOn (cost_continuousOn hs t x)).bddBelow ⟨z,hz,rfl⟩)

lemma envelope_frontier {S : Set X} {s : X → ℝ} (hS : IsCompact S) (hs : ContinuousOn s S)
    (cap t : ℝ) {x : X} (hx : x ∈ S) : envelope S s cap t x ≤ s x := by
  simpa only [dist_self,mul_zero,add_zero] using envelope_le_cost hS hs cap t x hx

lemma envelope_cases {S : Set X} {s : X → ℝ} (hS : IsCompact S) (hs : ContinuousOn s S)
    (cap t : ℝ) (x : X) :
    envelope S s cap t x = cap ∨
      ∃ z ∈ S, envelope S s cap t x = s z+t*dist x z := by
  classical
  by_cases hn : S.Nonempty
  · obtain ⟨z,hz,he⟩ := inf_attained hS hs hn t x
    rw [envelope,ite_eq_left hn,he]
    rcases le_total cap (s z+t*dist x z) with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr ⟨z,hz,min_eq_right h⟩
  · exact Or.inl (by rw [envelope,ite_eq_right hn])

lemma envelope_one_sided {S : Set X} {s : X → ℝ} (hS : IsCompact S)
    (hs : ContinuousOn s S) (cap : ℝ) {t : ℝ} (ht : 0 ≤ t) (x y : X) :
    envelope S s cap t x ≤ envelope S s cap t y+t*dist x y := by
  obtain h | ⟨z,hz,h⟩ := envelope_cases hS hs cap t y
  · rw [h]
    exact (envelope_le_cap S s cap t x).trans (le_add_of_nonneg_right (mul_nonneg ht dist_nonneg))
  · rw [h]
    have hc := envelope_le_cost hS hs cap t x hz
    have hm := mul_le_mul_of_nonneg_left (dist_triangle x y z) ht
    linarith

lemma envelope_lipschitz {S : Set X} {s : X → ℝ} (hS : IsCompact S)
    (hs : ContinuousOn s S) (cap : ℝ) (t : ℝ≥0) : LipschitzWith t (envelope S s cap t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,abs_le]
  have ha := envelope_one_sided hS hs cap t.coe_nonneg x y
  have hb := envelope_one_sided hS hs cap t.coe_nonneg y x
  rw [dist_comm y x] at hb
  constructor <;> linarith

/-- Single kept-cell clipping, before chart identifiers/rebasing. -/
noncomputable def clip (s F H : X → ℝ) (x : X) : ℝ := max (s x) (min (F x) (H x))

lemma clip_lipschitz {s F H : X → ℝ} {K : ℝ≥0}
    (hs : LipschitzWith K s) (hF : LipschitzWith K F) (hH : LipschitzWith K H) :
    LipschitzWith K (clip s F H) := by
  unfold clip
  simpa only [max_self] using hs.max (hF.min hH)

omit [PseudoMetricSpace X] in
lemma clip_unchanged {s F H : X → ℝ} {x : X} (h : F x ≤ s x ∨ H x ≤ s x) :
    clip s F H x = s x := by
  apply max_eq_left
  rcases h with h | h
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans h

omit [PseudoMetricSpace X] in
lemma clip_movement {s F H : X → ℝ} {B : ℝ} (hB : 0 ≤ B) (x : X)
    (hF : F x ≤ s x+B) : 0 ≤ clip s F H x-s x ∧ clip s F H x-s x ≤ B := by
  constructor
  · exact sub_nonneg.mpr (le_max_left _ _)
  · have : clip s F H x ≤ s x+B := max_le (by linarith) ((min_le_left _ _).trans hF)
    linarith

/-- The source main raise-or-descend alternative, including the empty frontier.
The radius interval is obtained from actual radial padding and weak diameter
when this lemma is applied to the literal full-column frontier. -/
lemma raise_or_descending_endpoint {S : Set X} {s F H : X → ℝ}
    (hS : IsCompact S) (hs : ContinuousOn s S) (w : X) (cap ζ E ε : ℝ)
    (happrox : envelope S s cap (1-ζ) w-5*E ≤ F w)
    (hshield : s w+2*E < H w) (hcap : s w+7*E < cap)
    (hrad : ∀ z ∈ S, (0.00001:ℝ) ≤ dist w z ∧ dist w z ≤ 0.02)
    (hzeta : 0 ≤ ζ) (herr : ζ*0.02+7*E ≤ ε) :
    s w+2*E < clip s F H w ∨
      ∃ z ∈ S, (0.00001:ℝ) ≤ dist w z ∧ dist w z ≤ 0.02 ∧
        s z ≤ s w-dist w z+ε := by
  by_cases hraise : s w+2*E < clip s F H w
  · exact Or.inl hraise
  · right
    have hc : min (F w) (H w) ≤ s w+2*E :=
      (le_max_right _ _).trans (not_lt.mp hraise)
    have hFw : F w ≤ s w+2*E := (min_le_iff.mp hc).resolve_right (not_le.mpr hshield)
    have he : envelope S s cap (1-ζ) w ≤ s w+7*E := by linarith
    obtain h | ⟨z,hz,h⟩ := envelope_cases hS hs cap (1-ζ) w
    · rw [h] at he
      exact (not_le.mpr hcap he).elim
    · refine ⟨z,hz,(hrad z hz).1,(hrad z hz).2,?_⟩
      rw [h] at he
      have hm := mul_le_mul_of_nonneg_left (hrad z hz).2 hzeta
      nlinarith

end PlanarL1.Clipping


end

section

namespace PlanarL1.Clipping
open scoped NNReal

/-- Literal trapezoidal height branch, constant outside the closed band. -/
noncomputable def heightShield (lo a s α H : ℝ) : ℝ :=
  s-1+α + 3 * min 1 (max 0 (min (H-lo) (lo+a-H)) / (9*a/100))

lemma heightShield_left {lo a s α H : ℝ} (hH : H ≤ lo) :
    heightShield lo a s α H = s-1+α := by
  have hm : min (H-lo) (lo+a-H) ≤ 0 := (min_le_left _ _).trans (sub_nonpos.mpr hH)
  simp only [heightShield,max_eq_left hm,zero_div,min_eq_right (by norm_num : (0:ℝ) ≤ 1),mul_zero,add_zero]

lemma heightShield_right {lo a s α H : ℝ} (hH : lo+a ≤ H) :
    heightShield lo a s α H = s-1+α := by
  have hm : min (H-lo) (lo+a-H) ≤ 0 := (min_le_right _ _).trans (sub_nonpos.mpr hH)
  simp only [heightShield,max_eq_left hm,zero_div,min_eq_right (by norm_num : (0:ℝ) ≤ 1),mul_zero,add_zero]

lemma heightShield_plateau {lo a s α H : ℝ} (ha : 0 < a)
    (hl : lo+9*a/100 ≤ H) (hr : H ≤ lo+a-9*a/100) :
    heightShield lo a s α H = s+2+α := by
  have hb : 0 < 9*a/100 := by positivity
  have hm : 9*a/100 ≤ min (H-lo) (lo+a-H) := le_min (by linarith) (by linarith)
  have hq : 1 ≤ max 0 (min (H-lo) (lo+a-H)) / (9*a/100) := by
    apply (le_div_iff₀ hb).mpr
    simpa only [one_mul] using hm.trans (le_max_right _ _)
  rw [heightShield,min_eq_left hq]
  ring

lemma heightShield_bounds {lo a s α H : ℝ} (ha : 0 < a) :
    s-1+α ≤ heightShield lo a s α H ∧ heightShield lo a s α H ≤ s+2+α := by
  have hb : 0 < 9*a/100 := by positivity
  have hz : 0 ≤ min 1 (max 0 (min (H-lo) (lo+a-H)) / (9*a/100)) :=
    le_min (by norm_num) (div_nonneg (le_max_left _ _) hb.le)
  have ho := min_le_left (1:ℝ) (max 0 (min (H-lo) (lo+a-H)) / (9*a/100))
  dsimp only [heightShield]
  constructor <;> linarith

lemma heightShield_lipschitz (lo s α : ℝ) {a : ℝ} (ha : 0 < a) :
    LipschitzWith ⟨3/(9*a/100),by positivity⟩ (heightShield lo a s α) := by
  have hb : 0 < 9*a/100 := by positivity
  have hl : LipschitzWith 1 (fun H : ℝ => H-lo) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_sub_right,NNReal.coe_one,one_mul,le_refl]
  have hr : LipschitzWith 1 (fun H : ℝ => lo+a-H) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_sub_left,NNReal.coe_one,one_mul,le_refl]
  have hm : LipschitzWith 1 (fun H : ℝ => max 0 (min (H-lo) (lo+a-H))) := by
    simpa only [max_self, max_eq_right (show (0:ℝ≥0) ≤ 1 by norm_num)] using
      (LipschitzWith.const (0:ℝ)).max (hl.min hr)
  have hq : LipschitzWith ⟨1/(9*a/100),by positivity⟩
      (fun H : ℝ => max 0 (min (H-lo) (lo+a-H))/(9*a/100)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist _ _ ≤ (1/(9*a/100))*dist x y
    rw [Real.dist_eq,← sub_div,abs_div,abs_of_pos hb]
    have h := hm.dist_le_mul x y
    rw [Real.dist_eq,NNReal.coe_one,one_mul] at h
    calc
      _ ≤ dist x y/(9*a/100) := div_le_div_of_nonneg_right h hb.le
      _ = _ := by ring
  have hp : LipschitzWith ⟨1/(9*a/100),by positivity⟩
      (fun H : ℝ => min 1 (max 0 (min (H-lo) (lo+a-H))/(9*a/100))) := by
    exact hq.const_min 1
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hp.dist_le_mul x y
  change dist _ _ ≤ (1/(9*a/100))*dist x y at h
  rw [Real.dist_eq] at h
  change dist _ _ ≤ (3/(9*a/100))*dist x y
  rw [heightShield,heightShield,Real.dist_eq]
  let f (H : ℝ) := min 1 (max 0 (min (H-lo) (lo+a-H))/(9*a/100))
  change |(s-1+α+3*f x)-(s-1+α+3*f y)| ≤ (3/(9*a/100))*dist x y
  change |f x-f y| ≤ (1/(9*a/100))*dist x y at h
  calc
    _ = 3*|f x-f y| := by
      rw [show (s-1+α+3*f x)-(s-1+α+3*f y) = 3*(f x-f y) by ring,
        abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 3)]
    _ ≤ 3*((1/(9*a/100))*dist x y) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

end PlanarL1.Clipping


end

section

namespace PlanarL1.Clipping
variable {X : Type*}

noncomputable def orderedBranch (pc radius α : ℝ) (L : X → ℝ) (x : X) : ℝ :=
  pc+radius/20+4*(L x-pc)+α

lemma orderedBranch_boundary {pc radius α p : ℝ} {L : X → ℝ} {x : X}
    (hα : α ≤ radius/1000) (hL : L x ≤ p) (hp : p < pc-(65/100:ℝ)*radius) :
    orderedBranch pc radius α L x < p-(1899/1000:ℝ)*radius := by
  dsimp only [orderedBranch]
  linarith

lemma orderedBranch_seed {pc radius α p : ℝ} {L : X → ℝ} {x : X} (hr : 0 < radius)
    (hα : 0 ≤ α) (hL : |L x-pc| ≤ (10/1000000:ℝ)*radius)
    (hp : |p-pc| ≤ (60/1000000:ℝ)*radius) :
    p+radius/25 < orderedBranch pc radius α L x := by
  have hl := (abs_le.mp hL).1
  have hu := (abs_le.mp hp).2
  dsimp only [orderedBranch]
  linarith

lemma ordinary_boundary_margin {pc radius α p T : ℝ} {L : X → ℝ} {x : X} (hr : 0 ≤ radius)
    (hα : α ≤ radius/1000) (hL : L x ≤ p) (hT : T ≤ pc-(849/1000:ℝ)*radius) :
    min T (orderedBranch pc radius α L x) ≤ p-(199/1000:ℝ)*radius := by
  by_cases hp : pc-(65/100:ℝ)*radius ≤ p
  · exact (min_le_left _ _).trans (by linarith)
  · have ho := orderedBranch_boundary hα hL (lt_of_not_ge hp)
    exact (min_le_right _ _).trans (by linarith)

end PlanarL1.Clipping




end

end OAI
