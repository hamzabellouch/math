import OAI.Geometry.RCD.Heat.TimeLowerEnvelope

namespace OAI

/-! # Convergence between dense time slices

A vanishing one-sided time error suffices for convergence at every
continuity point of the bounded monotone envelope.
-/

open Set Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem almost_monotone_time_limit
    {δ M : ℝ} (hM : 0 ≤ M) (s v : ℕ → ℝ)
    (hs : ∀ i, s i ∈ Icc δ 1)
    (hdense : ∀ a b : ℝ, δ ≤ a → b ≤ 1 → a < b → ∃ i, a < s i ∧ s i < b)
    (f : ℕ → ℝ → ℝ) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ k t, t ∈ Icc δ 1 → |f k t| ≤ M)
    (hv : ∀ i, |v i| ≤ M)
    (hl : ∀ i, Tendsto (fun k => f k (s i)) atTop (𝓝 (v i)))
    (ho : ∀ k a b, δ ≤ a → a ≤ b → b ≤ 1 → f k a-f k b ≤ e k*(b-a))
    {t : ℝ} (ht : t ∈ Ioo δ 1)
    (hc : ContinuousAt (timeLowerEnvelope M s v) t) :
    Tendsto (fun k => f k t) atTop (𝓝 (timeLowerEnvelope M s v t)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨y,hy,hay⟩ := exists_lt_of_lt_csSup
      (show ({-M} ∪ {y | ∃ i, s i < t ∧ y = v i}).Nonempty from
        ⟨-M,Or.inl (mem_singleton _)⟩) ha
    rcases hy with hy | ⟨i,hit,rfl⟩
    · have haM : a < -M := by simpa only [mem_singleton_iff.mp hy] using hay
      exact Eventually.of_forall fun k => haM.trans_le (abs_le.mp (hb k t ⟨ht.1.le,ht.2.le⟩)).1
    · have her : Tendsto (fun k => e k*(t-s i)) atTop (𝓝 0) := by
        simpa only [zero_mul] using he.mul_const (t-s i)
      have hlim : Tendsto (fun k => f k (s i)-e k*(t-s i)) atTop (𝓝 (v i)) := by
        simpa only [sub_zero] using (hl i).sub her
      filter_upwards [(tendsto_order.mp hlim).1 a hay] with k hk
      have hh := ho k (s i) t (hs i).1 hit.le ht.2.le
      linarith
  · intro a ha
    have hnh : {u : ℝ | timeLowerEnvelope M s v u < a} ∈ 𝓝 t :=
      hc.preimage_mem_nhds (Iio_mem_nhds ha)
    obtain ⟨l,b,htlb,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnh
    let u := (t+min b 1)/2
    have htu : t < u := by dsimp only [u]; have := lt_min htlb.2 ht.2; linarith
    have hub : u < b := by
      dsimp only [u]
      have := min_le_left b 1
      linarith [htlb.2]
    have hu1 : u < 1 := by
      dsimp only [u]
      have := min_le_right b 1
      linarith [ht.2]
    have hua : timeLowerEnvelope M s v u < a := hsub ⟨htlb.1.trans htu,hub⟩
    obtain ⟨i,hti,hiu⟩ := hdense t u ht.1.le hu1.le htu
    have hia : v i < a := (sample_le_timeLowerEnvelope hM s v hv hiu).trans_lt hua
    have her : Tendsto (fun k => e k*(s i-t)) atTop (𝓝 0) := by
      simpa only [zero_mul] using he.mul_const (s i-t)
    have hlim : Tendsto (fun k => f k (s i)+e k*(s i-t)) atTop (𝓝 (v i)) := by
      simpa only [add_zero] using (hl i).add her
    filter_upwards [(tendsto_order.mp hlim).2 a hia] with k hk
    have hh := ho k t (s i) ht.1.le hti.le (hs i).2
    linarith

end RegularPointCoordinates

end

end OAI
