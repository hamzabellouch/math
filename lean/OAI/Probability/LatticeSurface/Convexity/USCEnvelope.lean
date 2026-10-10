import Mathlib

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E]

def hypo (K : Set E) (f : E → ℝ) : Set (E × ℝ) := {z | z.1∈K ∧ 0≤z.2 ∧ z.2≤f z.1}

def envelope (K : Set E) (f : E → ℝ) (k : ℕ) (x : E) : ℝ :=
  sSup ((fun z : E × ℝ => z.2*Real.exp (-(k:ℝ)*dist x z.1)) '' hypo K f)

lemma compact_hypo {K : Set E} {f : E → ℝ} (hK : IsCompact K)
    (hf : UpperSemicontinuous f) : IsCompact (hypo K f) := by
  obtain ⟨M,hM⟩ := (hf.upperSemicontinuousOn K).bddAbove_of_isCompact hK
  have hc : IsClosed (hypo K f) := by
    have hh := upperSemicontinuous_iff_IsClosed_hypograph.mp hf
    exact hK.isClosed.preimage continuous_fst |>.inter
      ((isClosed_le continuous_const continuous_snd).inter hh)
  apply (hK.prod (isCompact_Icc (a:=0) (b:=max 0 M))).of_isClosed_subset hc
  intro z hz
  exact ⟨hz.1,hz.2.1,(hz.2.2.trans (hM (mem_image_of_mem f hz.1))).trans (le_max_right _ _)⟩

omit [NormedAddCommGroup E] in
lemma nonempty_hypo {K : Set E} {f : E → ℝ} (hne : K.Nonempty)
    (hf0 : ∀ x∈K,0≤f x) : (hypo K f).Nonempty := by
  obtain ⟨x,hx⟩ := hne
  exact ⟨(x,0),hx,le_rfl,hf0 x hx⟩

lemma continuous_kernel (k : ℕ) :
    Continuous (fun p : E × (E × ℝ) => p.2.2*Real.exp (-(k:ℝ)*dist p.1 p.2.1)) := by
  fun_prop

lemma continuous_envelope {K : Set E} {f : E → ℝ} (hK : IsCompact K)
    (hf : UpperSemicontinuous f) (k : ℕ) : Continuous (envelope K f k) :=
  (compact_hypo hK hf).continuous_sSup (continuous_kernel k)

lemma envelope_max {K : Set E} {f : E → ℝ} (hK : IsCompact K)
    (hf : UpperSemicontinuous f) (hne : K.Nonempty) (hf0 : ∀ x∈K,0≤f x)
    (k : ℕ) (x : E) : ∃ z∈hypo K f,
      envelope K f k x=z.2*Real.exp (-(k:ℝ)*dist x z.1) := by
  exact (compact_hypo hK hf).exists_sSup_image_eq (nonempty_hypo hne hf0)
    ((continuous_kernel k).comp (.prodMk_right x)).continuousOn

lemma le_envelope {K : Set E} {f : E → ℝ} (hK : IsCompact K)
    (hf : UpperSemicontinuous f) (k : ℕ) (x : E) {z : E × ℝ} (hz : z∈hypo K f) :
    z.2*Real.exp (-(k:ℝ)*dist x z.1)≤envelope K f k x := by
  apply le_csSup ((compact_hypo hK hf).bddAbove_image
    ((continuous_kernel k).comp (.prodMk_right x)).continuousOn)
  exact mem_image_of_mem _ hz

lemma self_le_envelope {K : Set E} {f : E → ℝ} (hK : IsCompact K)
    (hf : UpperSemicontinuous f) (hf0 : ∀ x∈K,0≤f x) (k : ℕ) {x : E} (hx : x∈K) :
    f x≤envelope K f k x := by
  simpa using le_envelope hK hf k x (z:=(x,f x)) ⟨hx,hf0 x hx,le_rfl⟩

lemma envelope_nonneg {K : Set E} {f : E → ℝ} (hK : IsCompact K)
    (hf : UpperSemicontinuous f) (hne : K.Nonempty) (hf0 : ∀ x∈K,0≤f x)
    (k : ℕ) (x : E) : 0≤envelope K f k x := by
  obtain ⟨z,hz,heq⟩ := envelope_max hK hf hne hf0 k x
  rw [heq]
  exact mul_nonneg hz.2.1 (Real.exp_pos _).le

lemma envelope_pos {K : Set E} {f : E → ℝ} (hK : IsCompact K)
    (hf : UpperSemicontinuous f) (hpos : ∃ z∈K,0<f z) (k : ℕ) (x : E) :
    0<envelope K f k x := by
  obtain ⟨z,hz,hfz⟩ := hpos
  exact (mul_pos hfz (Real.exp_pos _)).trans_le
    (le_envelope hK hf k x (z:=(z,f z)) ⟨hz,hfz.le,le_rfl⟩)

lemma envelope_bound {K : Set E} {f : E → ℝ} (hK : IsCompact K)
    (hf : UpperSemicontinuous f) (hne : K.Nonempty) (hf0 : ∀ x∈K,0≤f x)
    {M : ℝ} (hM : ∀ x∈K,f x≤M) (k : ℕ) (x : E) : envelope K f k x≤M := by
  obtain ⟨z,hz,heq⟩ := envelope_max hK hf hne hf0 k x
  rw [heq]
  have he : Real.exp (-(k:ℝ)*dist x z.1)≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) dist_nonneg)
  calc
    _ ≤ z.2*1 := mul_le_mul_of_nonneg_left he hz.2.1
    _ ≤ M := by simpa using hz.2.2.trans (hM z.1 hz.1)

lemma tendsto_envelope {K : Set E} {f : E → ℝ} (hK : IsCompact K)
    (hf : UpperSemicontinuous f) (hf0 : ∀ x∈K,0≤f x) {x : E} (hx : x∈K) :
    Tendsto (fun k => envelope K f k x) atTop (𝓝 (f x)) := by
  obtain ⟨M,hM⟩ := (hf.upperSemicontinuousOn K).bddAbove_of_isCompact hK
  have hbd : ∀ z∈K,f z≤M := fun z hz => hM (mem_image_of_mem f hz)
  have hM0 : 0≤M := (hf0 x hx).trans (hbd x hx)
  refine tendsto_order.2 ⟨?_,?_⟩
  · intro b hb
    exact Eventually.of_forall fun k => hb.trans_le (self_le_envelope hK hf hf0 k hx)
  · intro b hb
    obtain ⟨δ,hδ,hnear⟩ := Metric.mem_nhds_iff.mp (hf x b hb)
    have hlim : Tendsto (fun k : ℕ => M*Real.exp (-(k:ℝ)*δ)) atTop (𝓝 0) := by
      have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop).atTop_mul_const hδ)
      simpa only [mul_zero,Function.comp_def,neg_mul] using ht.const_mul M
    have hb0 : 0<b := (hf0 x hx).trans_lt hb
    filter_upwards [(tendsto_order.1 hlim).2 b hb0] with k hk
    obtain ⟨z,hz,heq⟩ := envelope_max hK hf ⟨x,hx⟩ hf0 k x
    rw [heq]
    have he : Real.exp (-(k:ℝ)*dist x z.1)≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) dist_nonneg)
    by_cases hd : dist z.1 x<δ
    · have hzbd : z.2<b := hz.2.2.trans_lt (hnear (by exact hd))
      exact (mul_le_mul_of_nonneg_left he hz.2.1).trans_lt (by simpa using hzbd)
    · have hd' : δ≤dist x z.1 := by simpa [dist_comm] using le_of_not_gt hd
      have he' : Real.exp (-(k:ℝ)*dist x z.1)≤Real.exp (-(k:ℝ)*δ) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left hd' (neg_nonpos.mpr (Nat.cast_nonneg _))
      exact (mul_le_mul (hz.2.2.trans (hbd z.1 hz.1)) he'
        (Real.exp_pos _).le hM0).trans_lt hk

variable [NormedSpace ℝ E]

lemma dist_combination {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x y u v : E) :
    dist (s • x+t • y) (s • u+t • v)≤ s*dist x u+t*dist y v := by
  calc
    _ = ‖s • (x-u)+t • (y-v)‖ := by rw [dist_eq_norm];congr 1;module
    _ ≤ ‖s • (x-u)‖+‖t • (y-v)‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul,norm_smul,Real.norm_of_nonneg hs,Real.norm_of_nonneg ht,
      ← dist_eq_norm,← dist_eq_norm]

lemma envelope_combination {K : Set E} {f g h : E → ℝ} {s t : ℝ}
    (hK : IsCompact K) (hKc : Convex ℝ K) (hne : K.Nonempty)
    (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) (hh : UpperSemicontinuous h)
    (hf0 : ∀ x∈K,0≤f x) (hg0 : ∀ x∈K,0≤g x)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t=1)
    (hcomb : ∀ x∈K,∀ y∈K,(f x)^s*(g y)^t≤h (s • x+t • y))
    (k : ℕ) (x y : E) :
    (envelope K f k x)^s*(envelope K g k y)^t≤envelope K h k (s • x+t • y) := by
  obtain ⟨u,hu,heu⟩ := envelope_max hK hf hne hf0 k x
  obtain ⟨v,hv,hev⟩ := envelope_max hK hg hne hg0 k y
  let a := (u.2)^s*(v.2)^t
  have ha : 0≤a := mul_nonneg (Real.rpow_nonneg hu.2.1 _) (Real.rpow_nonneg hv.2.1 _)
  have haw : a≤h (s • u.1+t • v.1) := by
    calc
      _ ≤ (f u.1)^s*(g v.1)^t := mul_le_mul (Real.rpow_le_rpow hu.2.1 hu.2.2 hs)
        (Real.rpow_le_rpow hv.2.1 hv.2.2 ht) (Real.rpow_nonneg hv.2.1 _) (Real.rpow_nonneg (hf0 _ hu.1) _)
      _ ≤ _ := hcomb _ hu.1 _ hv.1
  have hm := le_envelope hK hh k (s • x+t • y)
    (z:=(s • u.1+t • v.1,a)) ⟨hKc hu.1 hv.1 hs ht hst,ha,haw⟩
  rw [heu,hev]
  rw [Real.mul_rpow hu.2.1 (Real.exp_pos _).le,Real.mul_rpow hv.2.1 (Real.exp_pos _).le]
  rw [← Real.exp_mul,← Real.exp_mul]
  calc
    _ = a*Real.exp (-(k:ℝ)*(s*dist x u.1+t*dist y v.1)) := by
      dsimp [a];rw [show -(k:ℝ)*(s*dist x u.1+t*dist y v.1)=
        (-(k:ℝ)*dist x u.1)*s+(-(k:ℝ)*dist y v.1)*t by ring,Real.exp_add];ring
    _ ≤ a*Real.exp (-(k:ℝ)*dist (s • x+t • y) (s • u.1+t • v.1)) := by
      apply mul_le_mul_of_nonneg_left _ ha
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (dist_combination hs ht x y u.1 v.1)
        (neg_nonpos.mpr (Nat.cast_nonneg _))
    _ ≤ _ := hm

end USCEnvelope

end

end OAI
