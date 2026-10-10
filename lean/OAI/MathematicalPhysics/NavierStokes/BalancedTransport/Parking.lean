import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Motion

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def CenterSeparated (a : ι → Space) (D : ℝ) : Prop :=
  ∀ i j, i ≠ j → ∃ k, D < |a i k - a j k|

omit [Fintype ι] in
lemma CenterSeparated.update {a : ι → Space} {D : ℝ} (ha : CenterSeparated a D)
    (i : ι) (b : Space) (hb : ∀ j, j ≠ i → ∃ k, D < |b k - a j k|) :
    CenterSeparated (Function.update a i b) D := by
  intro j k hjk
  by_cases hji : j = i
  · subst j
    simpa [Function.update_of_ne (Ne.symm hjk)] using hb k (Ne.symm hjk)
  · by_cases hki : k = i
    · subst k
      obtain ⟨l, hl⟩ := hb j hji
      exact ⟨l, by simpa [Function.update_of_ne hji, abs_sub_comm] using hl⟩
    · simpa [Function.update_of_ne hji, Function.update_of_ne hki] using ha j k hjk

omit [Fintype ι] [DecidableEq ι] in
lemma separated_of_centerSeparated {a w : ι → Space} {D η : ℝ}
    (ha : CenterSeparated a D) (hw : ∀ i j k, w i k + w j k + 4 * η ≤ D) :
    (BoxLayout.mk a w).Separated η := by
  intro i j hij
  obtain ⟨k, hk⟩ := ha i j hij
  exact ⟨k, lt_of_le_of_lt (hw i j k) hk⟩

omit [Fintype ι] in
lemma segment_center_eq {a : ι → Space} (i : ι) (b _w : Space) (r : ℝ) :
    (fun j k => (1 - r) * a j k + r * (Function.update a i b) j k) =
      Function.update a i (fun k => (1 - r) * a i k + r * b k) := by
  ext j k
  by_cases hji : j = i
  · subst j; simp
  · simp only [Function.update_of_ne hji]
    ring

def singleSegmentMotion {a w : ι → Space} {D η : ℝ} {safe : Set ι}
    (i : ι) (b : Space) (hp : ∀ j k, 0 < w j k)
    (hw : ∀ j l k, w j k + w l k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hb : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * a i k + r * b k - a j k|)
    (hga : (BoxLayout.mk a w).Guarded safe)
    (hgb : (BoxLayout.mk (Function.update a i b) w).Guarded safe) :
    BoxMotion ⟨a, w⟩ ⟨Function.update a i b, w⟩ safe η :=
  segmentMotion hp (by
    intro r hr
    apply separated_of_centerSeparated _ hw
    change CenterSeparated (fun j k => (1 - r) * a j k + r * (Function.update a i b) j k) D
    rw [segment_center_eq i b (0 : Space) r]
    exact ha.update i _ (hb r hr))
    (fun _ hr => segment_guard hga hgb hr)

omit [Fintype ι] in
lemma guarded_update {a w : ι → Space} {safe : Set ι}
    (ha : (BoxLayout.mk a w).Guarded safe) (i : ι) (b : Space)
    (hb : i ∈ safe → 2 < b 0 - w i 0) :
    (BoxLayout.mk (Function.update a i b) w).Guarded safe := by
  intro j hj
  by_cases hji : j = i
  · subst j; simpa using hb hj
  · simpa [Function.update_of_ne hji] using ha j hj

lemma raising_gap {p q : Space} {H r D : ℝ} (hq : q 1 ≤ p 1) (hH : p 1 ≤ H)
    (hr : r ∈ Icc (0 : ℝ) 1) (hgap : ∃ k, D < |p k - q k|) :
    ∃ k, D < |(1 - r) * p k + r * (Function.update p 1 H) k - q k| := by
  obtain ⟨k, hk⟩ := hgap
  by_cases hk₁ : k = 1
  · subst k
    refine ⟨1, ?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hq)] at hk
    have hh : 0 ≤ (1 - r) * p 1 + r * H - q 1 := by
      nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr hH)]
    simp only [Function.update_self, abs_of_nonneg hh]
    nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr hH)]
  · refine ⟨k, ?_⟩
    rw [Function.update_of_ne hk₁]
    convert hk using 1; congr 1; ring

lemma high_plane_gap {p q z : Space} {H r D : ℝ} (hp : p 1 = H) (hq : q 1 = H)
    (hz : D < H - z 1) :
    ∃ k, D < |(1 - r) * p k + r * q k - z k| := by
  refine ⟨1, hz.trans_le ?_⟩
  rw [hp, hq]
  calc
    H - z 1 = (1 - r) * H + r * H - z 1 := by ring
    _ ≤ |(1 - r) * H + r * H - z 1| := le_abs_self _

lemma fixed_first_gap {p q z : Space} {r D : ℝ} (hpq : p 0 = q 0)
    (hz : D < |q 0 - z 0|) :
    ∃ k, D < |(1 - r) * p k + r * q k - z k| := by
  refine ⟨0, ?_⟩
  rw [hpq]
  convert hz using 1; congr 1; ring

def remainingCenters (a p : ι → Space) (S : Finset ι) (i : ι) : Space :=
  if i ∈ S then a i else p i

omit [Fintype ι] in
lemma remainingCenters_separated {a p : ι → Space} {D : ℝ}
    (ha : CenterSeparated a D)
    (hcross : ∀ i j, D < |a i 0 - p j 0|)
    (hp : ∀ i j, i ≠ j → D < |p i 0 - p j 0|) (S : Finset ι) :
    CenterSeparated (remainingCenters a p S) D := by
  intro i j hij
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simpa [remainingCenters, hi, hj] using ha i j hij
  · exact ⟨0, by simpa [remainingCenters, hi, hj] using hcross i j⟩
  · exact ⟨0, by simpa [remainingCenters, hi, hj, abs_sub_comm] using hcross j i⟩
  · exact ⟨0, by simpa [remainingCenters, hi, hj] using hp i j hij⟩

omit [Fintype ι] in
lemma remainingCenters_guarded {a p w : ι → Space} {safe : Set ι}
    (ha : (BoxLayout.mk a w).Guarded safe) (hp : (BoxLayout.mk p w).Guarded safe)
    (S : Finset ι) : (BoxLayout.mk (remainingCenters a p S) w).Guarded safe := by
  intro i hi
  by_cases h : i ∈ S
  · simpa [remainingCenters, h] using ha i hi
  · simpa [remainingCenters, h] using hp i hi

omit [Fintype ι] in
lemma remainingCenters_erase {a p : ι → Space} {S : Finset ι} {i : ι} (_hi : i ∈ S) :
    remainingCenters a p (S.erase i) = Function.update (remainingCenters a p S) i (p i) := by
  ext j k
  by_cases hji : j = i
  · subst j; simp [remainingCenters]
  · simp [remainingCenters, hji]

def evacuateHighest {a p w : ι → Space} {D η H : ℝ} {safe : Set ι}
    (hwidth : ∀ i k, 0 < w i k)
    (hsize : ∀ i j k, w i k + w j k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hcross : ∀ i j, D < |a i 0 - p j 0|)
    (hp : ∀ i j, i ≠ j → D < |p i 0 - p j 0|)
    (hhigha : ∀ i, D < H - a i 1) (hhighp : ∀ i, D < H - p i 1)
    (hD : 0 ≤ D)
    (hga : (BoxLayout.mk a w).Guarded safe) (hgp : (BoxLayout.mk p w).Guarded safe)
    (S : Finset ι) (i : ι) (hi : i ∈ S) (hmax : ∀ j ∈ S, a j 1 ≤ a i 1) :
    BoxMotion ⟨remainingCenters a p S, w⟩ ⟨remainingCenters a p (S.erase i), w⟩ safe η := by
  let u := remainingCenters a p S
  let v₁ := Function.update (a i) 1 H
  let v₂ := Function.update (p i) 1 H
  have hui : u i = a i := by simp [u, remainingCenters, hi]
  have hu := remainingCenters_separated ha hcross hp S
  have hgu := remainingCenters_guarded hga hgp S
  have hv₁ : (BoxLayout.mk (Function.update u i v₁) w).Guarded safe :=
    guarded_update hgu i v₁ (by intro his; simpa [v₁] using hga i his)
  have hv₂ : (BoxLayout.mk (Function.update u i v₂) w).Guarded safe :=
    guarded_update hgu i v₂ (by intro his; simpa [v₂] using hgp i his)
  have hp₃ : (BoxLayout.mk (Function.update u i (p i)) w).Guarded safe :=
    guarded_update hgu i (p i) (fun his => hgp i his)
  have hfirst : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * u i k + r * v₁ k - u j k| := by
    intro r hr j hji
    rw [hui]
    by_cases hj : j ∈ S
    · have huj : u j = a j := by simp [u, remainingCenters, hj]
      rw [huj]
      exact raising_gap (hmax j hj) (by linarith [hhigha i]) hr (ha i j (Ne.symm hji))
    · have huj : u j = p j := by simp [u, remainingCenters, hj]
      rw [huj]
      exact fixed_first_gap (by simp [v₁]) (by simpa [v₁] using hcross i j)
  have hsecond : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * (Function.update u i v₁) i k +
        r * v₂ k - (Function.update u i v₁) j k| := by
    intro r _ j hji
    simp only [Function.update_self, Function.update_of_ne hji]
    apply high_plane_gap (H := H) (by simp [v₁]) (by simp [v₂])
    by_cases hj : j ∈ S
    · simpa [u, remainingCenters, hj] using hhigha j
    · simpa [u, remainingCenters, hj] using hhighp j
  have hthird : ∀ r ∈ Icc (0 : ℝ) 1, ∀ j, j ≠ i →
      ∃ k, D < |(1 - r) * (Function.update u i v₂) i k +
        r * p i k - (Function.update u i v₂) j k| := by
    intro r _ j hji
    simp only [Function.update_self, Function.update_of_ne hji]
    apply fixed_first_gap (by simp [v₂])
    by_cases hj : j ∈ S
    · simpa [u, remainingCenters, hj, abs_sub_comm] using hcross j i
    · simpa [u, remainingCenters, hj] using hp i j (Ne.symm hji)
  have hsep₁ := hu.update i v₁ (fun j hji => by simpa using hfirst 1 ⟨by norm_num, le_rfl⟩ j hji)
  have hsep₂ : CenterSeparated (Function.update u i v₂) D := by
    have hh := hsep₁.update i v₂ (fun j hji => by simpa using hsecond 1 ⟨by norm_num, le_rfl⟩ j hji)
    simpa [Function.update_idem] using hh
  let m₁ := singleSegmentMotion i v₁ hwidth hsize hu hfirst hgu hv₁
  let m₂ := singleSegmentMotion i v₂ hwidth hsize hsep₁ hsecond hv₁
    (by simpa [Function.update_idem] using hv₂)
  let m₃ := singleSegmentMotion i (p i) hwidth hsize hsep₂ hthird hv₂
    (by simpa [Function.update_idem] using hp₃)
  have m₂' : BoxMotion ⟨Function.update u i v₁, w⟩ ⟨Function.update u i v₂, w⟩ safe η :=
    by simpa [Function.update_idem] using m₂
  have m₃' : BoxMotion ⟨Function.update u i v₂, w⟩ ⟨Function.update u i (p i), w⟩ safe η :=
    by simpa [Function.update_idem] using m₃
  simpa [remainingCenters_erase hi] using (m₁.trans m₂').trans m₃'

def evacuateToParking {a p w : ι → Space} {D η H : ℝ} {safe : Set ι}
    (hwidth : ∀ i k, 0 < w i k)
    (hsize : ∀ i j k, w i k + w j k + 4 * η ≤ D)
    (ha : CenterSeparated a D)
    (hcross : ∀ i j, D < |a i 0 - p j 0|)
    (hp : ∀ i j, i ≠ j → D < |p i 0 - p j 0|)
    (hhigha : ∀ i, D < H - a i 1) (hhighp : ∀ i, D < H - p i 1)
    (hD : 0 ≤ D)
    (hga : (BoxLayout.mk a w).Guarded safe) (hgp : (BoxLayout.mk p w).Guarded safe) :
    BoxMotion ⟨a, w⟩ ⟨p, w⟩ safe η := by
  have h : ∀ S : Finset ι, Nonempty
      (BoxMotion ⟨remainingCenters a p S, w⟩ ⟨p, w⟩ safe η) := by
    intro S
    refine Finset.strongInductionOn S ?_
    intro S ih
    by_cases hS : S.Nonempty
    · obtain ⟨i, hi, hmax⟩ := S.exists_max_image (fun i => a i 1) hS
      obtain ⟨m⟩ := ih (S.erase i) (Finset.erase_ssubset hi)
      exact ⟨(evacuateHighest hwidth hsize ha hcross hp hhigha hhighp hD
        hga hgp S i hi hmax).trans m⟩
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      have hempty : remainingCenters a p ∅ = p := by ext i k; simp [remainingCenters]
      rw [hempty]
      exact ⟨BoxMotion.stationary (A := ⟨p, w⟩) hwidth
        (separated_of_centerSeparated (fun i j hij => ⟨0, hp i j hij⟩) hsize) hgp⟩
  have hh := h Finset.univ
  have he : remainingCenters a p Finset.univ = a := by ext i k; simp [remainingCenters]
  rw [he] at hh
  exact Classical.choice hh

end BalancedTransport.Geometry
end

end OAI
