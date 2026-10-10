import OAI.Geometry.RuledCovering.SingularOverlap

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singular_geometric_cover {p gamma : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hpg : 0 < 1+gamma*(p-2)) :
    ∀ᶠ c : ℝ in 𝓝[>] 0,
      tetrahedron ⊆ singularLower p gamma c ∪ singularUpper p gamma c ∪
        lowerTip (c^gamma) ∪ upperTip (c^gamma) := by
  obtain ⟨C,_,hinv⟩ := singular_inverse_small hp2
  obtain ⟨K,_,hover⟩ := singular_overlap_small (by linarith : 0 ≤ p) hp2.le
  have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hcut : Tendsto (fun c : ℝ => c*C*(c^gamma)^(p-2)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_assoc,mul_left_comm,mul_zero] using (singular_cutoff_small hpg).const_mul C
  have hKlim : Tendsto (fun c : ℝ => c*K) (𝓝[>] 0) (𝓝 0) := by simpa using h0.mul_const K
  filter_upwards [self_mem_nhdsWithin,h0.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    hcut.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    hKlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),overlap_error_eventually K]
    with c hc hc1 hcut hcK herr
  have hc : 0 < c := hc
  intro z hz
  obtain ⟨t,ht0,ht1,hx,hy,hz2⟩ := hz
  by_cases htip : t ≤ 2*c^gamma
  · exact Or.inl (Or.inr ⟨t,ht0,htip,hy,hz2⟩)
  by_cases htip' : 1-t ≤ 2*c^gamma
  · exact Or.inr ⟨1-t,by linarith,htip',hx,by rw [hz2]; congr 1; ring⟩
  have hx1 : |z 0| ≤ 1 := hx.trans (by linarith)
  have hy1 : |z 1| ≤ 1 := hy.trans ht1
  have hkx : |c*z 0| ≤ c := by simpa only [abs_mul,abs_of_pos hc,mul_one] using mul_le_mul_of_nonneg_left hx1 hc.le
  have hky : |-c*z 1| ≤ c := by simpa only [abs_mul,abs_neg,abs_of_pos hc,mul_one] using mul_le_mul_of_nonneg_left hy1 hc.le
  obtain ⟨zm,hm0,hm2,hmb,hem⟩ := hinv (c^gamma) c (z 1) t (c*z 0)
    (Real.rpow_pos_of_pos hc gamma) hc.le hcut.le (by linarith) ht1 hy hkx
  obtain ⟨zp,hp0,hp2',hpb,hep⟩ := hinv (c^gamma) c (z 0) (1-t) (-c*z 1)
    (Real.rpow_pos_of_pos hc gamma) hc.le hcut.le (by linarith) (by linarith) hx hky
  have hem0 := congrArg (fun w : Plane => w 0) hem
  have hem1 := congrArg (fun w : Plane => w 1) hem
  have hep0 := congrArg (fun w : Plane => w 0) hep
  have hep1 := congrArg (fun w : Plane => w 1) hep
  change z 1 = zm 0+(c*z 0)*singularField p zm 0 at hem0
  change t = zm 1+(c*z 0)*singularField p zm 1 at hem1
  change z 0 = zp 0+(-c*z 1)*singularField p zp 0 at hep0
  change 1-t = zp 1+(-c*z 1)*singularField p zp 1 at hep1
  have hceil := hover c (z 0) (z 1) zm zp hc.le hc1.le hcK.le herr hx1 hy1 hm2 hp2' hmb hpb
    (by linarith only [hem0]) (by linarith only [hep0]) (by nlinarith only [hem1,hep1])
  rcases hceil with hm | hp'
  · apply Or.inl ∘ Or.inl ∘ Or.inl
    refine ⟨zm,⟨hm0,hm2,hmb,hm⟩,z 0,hx1,?_⟩
    ext i
    fin_cases i
    · rfl
    · change z 1 = zm 0+z 0*(c*singularField p zm 0)
      nlinarith only [hem0]
    · change z 2 = Real.sqrt 2*(zm 1+z 0*(c*singularField p zm 1))
      rw [hz2]
      congr 1
      nlinarith only [hem1]
  · apply Or.inl ∘ Or.inl ∘ Or.inr
    refine ⟨zp,⟨hp0,hp2',hpb,hp'⟩,z 1,hy1,?_⟩
    ext i
    fin_cases i
    · change z 0 = zp 0-c*z 1*singularField p zp 0
      nlinarith only [hep0]
    · rfl
    · change z 2 = Real.sqrt 2*(1-(zp 1-c*z 1*singularField p zp 1))
      rw [hz2]
      congr 1
      nlinarith only [hep1]

end RuledApproximation

end

end OAI
