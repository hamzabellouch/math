import OAI.MeasureTheory.Falconer.Recursion.OrderedProfileIntervals

namespace OAI

/-! Prefix clipping for the finite low-slope merge algorithm. At most one
original interval is shortened; an undersized residual costs one minimum length. -/
namespace Falconer

noncomputable def clipProfilePrefix (u r : ℝ) : List (ℝ × ℝ) → List (ℝ × ℝ)
  | [] => []
  | c::S => if c.1+c.2 ≤ u then c::clipProfilePrefix u r S
      else if r ≤ u-c.1 then [(c.1,u-c.1)] else []

theorem clipProfilePrefix_length_le (u r : ℝ) (S : List (ℝ × ℝ)) :
    (clipProfilePrefix u r S).length ≤ S.length := by
  induction S with
  | nil => simp [clipProfilePrefix]
  | cons c S ih =>
    simp only [clipProfilePrefix]
    split_ifs <;> simp_all

theorem clipProfilePrefix_spec {u r : ℝ} {S : List (ℝ × ℝ)}
    (hmin : ∀ c ∈ S, r ≤ c.2) {d : ℝ × ℝ} (hd : d ∈ clipProfilePrefix u r S) :
    ∃ c ∈ S, d.1 = c.1 ∧ r ≤ d.2 ∧ d.2 ≤ c.2 ∧ d.1+d.2 ≤ u := by
  induction S with
  | nil => simp [clipProfilePrefix] at hd
  | cons c S ih =>
    simp only [clipProfilePrefix] at hd
    split_ifs at hd with hend hsize
    · rcases List.mem_cons.mp hd with he | hd
      · subst d
        exact ⟨c,by simp,rfl,hmin c (by simp),le_rfl,hend⟩
      · obtain ⟨v,hv,h1,h2,h3,h4⟩ := ih (fun v hv => hmin v (by simp [hv])) hd
        exact ⟨v,by simp [hv],h1,h2,h3,h4⟩
    · have he : d = (c.1,u-c.1) := by simpa only [List.mem_singleton] using hd
      subst d
      refine ⟨c,by simp,rfl,hsize,?_,?_⟩ <;> dsimp <;> linarith
    · simp at hd

theorem clipProfilePrefix_ordered {u r H : ℝ} {S : List (ℝ × ℝ)}
    (hord : S.Pairwise (fun c d => c.1+H ≤ d.1)) (hmin : ∀ c ∈ S, r ≤ c.2) :
    (clipProfilePrefix u r S).Pairwise (fun c d => c.1+H ≤ d.1) := by
  induction S with
  | nil => simp [clipProfilePrefix]
  | cons c S ih =>
    rw [List.pairwise_cons] at hord
    simp only [clipProfilePrefix]
    split_ifs
    · rw [List.pairwise_cons]
      refine ⟨?_,ih hord.2 (fun d hd => hmin d (by simp [hd]))⟩
      intro d hd
      obtain ⟨v,hv,he,_⟩ := clipProfilePrefix_spec (fun v hv => hmin v (by simp [hv])) hd
      simpa only [he] using hord.1 v hv
    · simp
    · simp

theorem clipProfilePrefix_loss {u r b : ℝ} (hr : 0 ≤ r) (hub : u ≤ b)
    {S : List (ℝ × ℝ)} (hord : S.Pairwise (fun c d => c.1+c.2 ≤ d.1))
    (hb : ∀ c ∈ S, c.1+c.2 ≤ b ∧ 0 ≤ c.2) :
    (S.map Prod.snd).sum ≤ (clipProfilePrefix u r S |>.map Prod.snd).sum+(b-u)+r := by
  induction S with
  | nil => simp only [clipProfilePrefix,List.map_nil,List.sum_nil]; linarith
  | cons c S ih =>
    rw [List.pairwise_cons] at hord
    have hc := hb c (by simp)
    have ht := ordered_interval_length_le hc.1 hord.2 (by
      intro d hd
      exact ⟨hord.1 d hd,hb d (by simp [hd])⟩)
    simp only [clipProfilePrefix]
    split_ifs with hend hsize
    · have hi := ih hord.2 (fun d hd => hb d (by simp [hd]))
      simp only [List.map_cons,List.sum_cons]
      linarith
    · simp only [List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,add_zero]
      linarith
    · simp only [List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,zero_add]
      linarith

theorem clipProfilePrefix_length_lt {u r : ℝ} (hr : 0 < r) {S : List (ℝ × ℝ)}
    (hmin : ∀ c ∈ S, r ≤ c.2) (hex : ∃ c ∈ S, u ≤ c.1) :
    (clipProfilePrefix u r S).length < S.length := by
  induction S with
  | nil => simp at hex
  | cons c S ih =>
    simp only [clipProfilePrefix]
    split_ifs with hend hsize
    · have hex' : ∃ d ∈ S, u ≤ d.1 := by
        obtain ⟨d,hd,hu⟩ := hex
        rcases List.mem_cons.mp hd with he | hd
        · subst d
          have hm := hmin c (by simp)
          linarith
        · exact ⟨d,hd,hu⟩
      simpa only [List.length_cons] using
        Nat.succ_lt_succ (ih (fun d hd => hmin d (by simp [hd])) hex')
    · cases S with
      | nil =>
        obtain ⟨d,hd,hu⟩ := hex
        have he : d = c := by simpa only [List.mem_singleton] using hd
        subst d
        linarith
      | cons d S => simp
    · simp

end Falconer

end OAI
