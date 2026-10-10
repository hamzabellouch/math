import OAI.Combinatorics.HalvingLines.PathLimits

namespace OAI

open Filter Topology

namespace PlanarHalving.Boundary
open Set Filter
open scoped Topology

lemma sum_cube_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i)^3 ≤ (s.card : ℝ)^2 * ∑ i ∈ s, (f i)^3 := by
  have hh := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s (f := f) (p := 3) (by norm_num) hf
  norm_num only [show (3 : ℝ)-1=2 by norm_num, Real.rpow_ofNat] at hh
  exact hh

lemma sum_angular_power_le {ι : Type*} (s : Finset ι) (θ : ι → ℝ)
    (hθ : ∀ i ∈ s, 0 ≤ θ i) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∑ i ∈ s, θ i ^ α) ≤ (s.card : ℝ)^(1-α) * (∑ i ∈ s, θ i)^α := by
  by_cases hs : s.Nonempty
  · have hc : 0 < (s.card : ℝ) := Nat.cast_pos.mpr hs.card_pos
    have hh := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s
      (f := fun i => θ i^α) (p := α⁻¹) ((one_le_inv₀ hα).mpr hα1)
      (fun i hi => Real.rpow_nonneg (hθ i hi) α)
    have hsum : 0 ≤ ∑ i ∈ s, θ i^α := Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (hθ i hi) α)
    have hsum' : 0 ≤ ∑ i ∈ s, θ i := Finset.sum_nonneg hθ
    have hev (i : ι) (hi : i ∈ s) : (θ i^α)^α⁻¹ = θ i := Real.rpow_rpow_inv (hθ i hi) hα.ne'
    simp_rw [Finset.sum_congr rfl hev] at hh
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg hsum _) hh hα.le
    rw [← Real.rpow_mul hsum,inv_mul_cancel₀ hα.ne',Real.rpow_one,
      Real.mul_rpow (Real.rpow_nonneg hc.le _) hsum',← Real.rpow_mul hc.le] at hp
    have he : (α⁻¹-1)*α = 1-α := by
      calc
        (α⁻¹-1)*α = α⁻¹*α - α := by ring
        _ = 1-α := by rw [inv_mul_cancel₀ hα.ne']
    rwa [he] at hp
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [he,Finset.sum_empty,Finset.card_empty,Nat.cast_zero]
    rw [Real.zero_rpow hα.ne',mul_zero]

end PlanarHalving.Boundary

namespace PlanarHalving.Boundary
open Set Filter
open scoped Topology

lemma high_mass_bound {ι : Type*} (S : Finset ι) (lam s : ι → ℝ)
    {q M H : ℝ} (hq : 0 < q) (hM : 0 < M)
    (hlam : ∀ i ∈ S, lam i ≤ q⁻¹)
    (htail : ∀ u > 0, ((S.filter fun i => u < s i).card : ℝ) ≤ H * u^(-(4:ℝ)/3)) :
    ∑ i ∈ S with M*q^(-(3:ℝ)/4) < s i, lam i ≤ H*M^(-(4:ℝ)/3) := by
  classical
  let t := M*q^(-(3:ℝ)/4)
  have ht : 0 < t := mul_pos hM (Real.rpow_pos_of_pos hq _)
  have hpow : t^(-(4:ℝ)/3) = M^(-(4:ℝ)/3)*q := by
    dsimp [t]
    rw [Real.mul_rpow hM.le (Real.rpow_nonneg hq.le _),← Real.rpow_mul hq.le]
    norm_num
  have hp := mul_le_mul_of_nonneg_right (htail t ht) (inv_nonneg.mpr hq.le)
  rw [hpow] at hp
  have hbound := Finset.sum_le_sum (s := S.filter (fun i => t < s i))
    (f := lam) (g := fun _ => q⁻¹) (fun i hi => hlam i (Finset.mem_filter.mp hi).1)
  simp only [Finset.sum_const, nsmul_eq_mul] at hbound
  apply hbound.trans
  convert hp using 1; field_simp

lemma activity_sum_bound {ι : Type*} (S : Finset ι) (μ b θ : ι → ℝ)
    {q B B₀ T α : ℝ} (hq : 0 ≤ q) (hB : 0 ≤ B) (_hT : 0 ≤ T)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hcard : (S.card : ℝ) ≤ q) (hb : ∑ i ∈ S, b i ≤ B₀)
    (hθ : ∀ i ∈ S, 0 ≤ θ i) (hθsum : ∑ i ∈ S, θ i ≤ T)
    (hμ : ∀ i ∈ S, μ i ≤ 2*b i+B*θ i^α) :
    ∑ i ∈ S, μ i ≤ 2*B₀+B*q^(1-α)*T^α := by
  have hsum0 : 0 ≤ ∑ i ∈ S, θ i := Finset.sum_nonneg hθ
  have hc := Real.rpow_le_rpow (Nat.cast_nonneg S.card) hcard (sub_nonneg.mpr hα1)
  have hθp := Real.rpow_le_rpow hsum0 hθsum hα.le
  have hpow := (sum_angular_power_le S θ hθ hα hα1).trans
    (mul_le_mul hc hθp (Real.rpow_nonneg hsum0 _) (Real.rpow_nonneg hq _))
  have hsum := Finset.sum_le_sum hμ
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hm := mul_le_mul_of_nonneg_left hpow hB
  nlinarith only [hsum,hb,hm]

lemma low_cube_bound {ι : Type*} (S : Finset ι) (lam μ s : ι → ℝ)
    {q M A U : ℝ} (hq : 0 < q) (hM : 0 < M) (hA : 0 ≤ A)
    (hcard : (S.card : ℝ) ≤ q)
    (hlam : ∀ i ∈ S, 0 ≤ lam i) (hμ : ∀ i ∈ S, 0 ≤ μ i) (hs : ∀ i ∈ S, 0 ≤ s i)
    (hmass : ∀ i ∈ S, (lam i)^3 ≤ A*(s i)^3*μ i)
    (hμsum : ∑ i ∈ S, μ i ≤ U) :
    (∑ i ∈ S with s i ≤ M*q^(-(3:ℝ)/4), lam i)^3 ≤
      A*M^3*q^(-(1:ℝ)/4)*U := by
  classical
  let t := M*q^(-(3:ℝ)/4)
  let L := S.filter (fun i => s i ≤ t)
  have ht : 0 < t := mul_pos hM (Real.rpow_pos_of_pos hq _)
  have hL (i : ι) (hi : i ∈ L) : i ∈ S ∧ s i ≤ t := Finset.mem_filter.mp hi
  have hμsumL : ∑ i ∈ L, μ i ≤ U :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun i hi _ => hμ i hi)).trans hμsum
  have hmassL : ∑ i ∈ L, (lam i)^3 ≤ A*t^3*U := by
    calc
      _ ≤ ∑ i ∈ L, A*t^3*μ i := by
        apply Finset.sum_le_sum
        intro i hi
        apply (hmass i (hL i hi).1).trans
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hs i (hL i hi).1) (hL i hi).2 3) hA)
          (hμ i (hL i hi).1)
      _ = A*t^3 * ∑ i ∈ L, μ i := by rw [Finset.mul_sum]
      _ ≤ A*t^3*U := mul_le_mul_of_nonneg_left hμsumL (by positivity)
  have hc : (L.card : ℝ) ≤ q := (Nat.cast_le.mpr (Finset.card_filter_le ..)).trans hcard
  have hcube := sum_cube_le L lam (fun i hi => hlam i (hL i hi).1)
  have hsumlam : 0 ≤ ∑ i ∈ L, (lam i)^3 := by
    exact Finset.sum_nonneg (fun i hi => pow_nonneg (hlam i (hL i hi).1) _)
  have hc2 : (L.card : ℝ)^2 ≤ q^2 := by nlinarith [show (0:ℝ) ≤ L.card from Nat.cast_nonneg _]
  have hbound := hcube.trans ((mul_le_mul_of_nonneg_right hc2 hsumlam).trans
    (mul_le_mul_of_nonneg_left hmassL (sq_nonneg q)))
  have he : q^2*t^3 = M^3*q^(-(1:ℝ)/4) := by
    dsimp [t]
    rw [mul_pow,← Real.rpow_mul_natCast hq.le]
    simp only [Nat.cast_ofNat]
    rw [← Real.rpow_ofNat q 2]
    calc
      q^(2:ℝ) * (M^3 * q^((-(3:ℝ)/4)*3)) =
        M^3*(q^(2:ℝ)*q^((-(3:ℝ)/4)*3)) := by ring
      _ = M^3*q^(-(1:ℝ)/4) := by rw [← Real.rpow_add hq]; congr 2; norm_num
  change (∑ i ∈ L, lam i)^3 ≤ _
  calc
    _ ≤ q^2*(A*t^3*U) := hbound
    _ = A*(q^2*t^3)*U := by ring
    _ = A*(M^3*q^(-(1:ℝ)/4))*U := by rw [he]
    _ = A*M^3*q^(-(1:ℝ)/4)*U := by ring

end PlanarHalving.Boundary

namespace PlanarHalving.Boundary
open Set Filter
open scoped Topology

lemma low_bound_tendsto_zero {q : ℕ → ℝ} (hq : ∀ n, 0 < q n)
    (hqtop : Tendsto q atTop atTop) {α : ℝ} (hα : (3:ℝ)/4 < α)
    (A M B₀ B T : ℝ) :
    Tendsto (fun n => A*M^3*(q n)^(-(1:ℝ)/4)*
      (2*B₀+B*(q n)^(1-α)*T^α)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => (q n)^(-(1:ℝ)/4)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (show (0:ℝ)<1/4 by norm_num)).comp hqtop
    convert hh using 1
    funext n
    rw [Function.comp_apply,neg_div]
  have h2 : Tendsto (fun n => (q n)^((3:ℝ)/4-α)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp hqtop
    convert hh using 1
    funext n
    rw [Function.comp_apply,neg_sub]
  have ht := (h1.const_mul (A*M^3*(2*B₀))).add
    (h2.const_mul (A*M^3*B*T^α))
  simp only [mul_zero,add_zero] at ht
  apply ht.congr
  intro n
  have he : (q n)^(-(1:ℝ)/4)*(q n)^(1-α) = (q n)^((3:ℝ)/4-α) := by
    rw [← Real.rpow_add (hq n)]
    congr 1
    ring
  calc
    _ = A*M^3*(2*B₀)*(q n)^(-(1:ℝ)/4) +
      A*M^3*B*T^α*((q n)^(-(1:ℝ)/4)*(q n)^(1-α)) := by rw [he]
    _ = _ := by ring

theorem mass_eq_zero {ι : Type*} (S : ℕ → Finset ι)
    (lam μ s b θ : ℕ → ι → ℝ) (q : ℕ → ℝ)
    {L A H B B₀ T α : ℝ}
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hα : (3:ℝ)/4 < α) (hα1 : α ≤ 1)
    (hq : ∀ n, 0 < q n) (hqtop : Tendsto q atTop atTop)
    (hcard : ∀ n, ((S n).card : ℝ) ≤ q n)
    (hlam0 : ∀ n i, i ∈ S n → 0 ≤ lam n i)
    (hlam1 : ∀ n i, i ∈ S n → lam n i ≤ (q n)⁻¹)
    (hμ0 : ∀ n i, i ∈ S n → 0 ≤ μ n i)
    (hs0 : ∀ n i, i ∈ S n → 0 ≤ s n i)
    (hθ0 : ∀ n i, i ∈ S n → 0 ≤ θ n i)
    (hmass : ∀ n i, i ∈ S n → (lam n i)^3 ≤ A*(s n i)^3*μ n i)
    (hactivity : ∀ n i, i ∈ S n → μ n i ≤ 2*b n i+B*(θ n i)^α)
    (hbsum : ∀ n, ∑ i ∈ S n, b n i ≤ B₀)
    (hθsum : ∀ n, ∑ i ∈ S n, θ n i ≤ T)
    (htail : ∀ n u, 0 < u → ((S n |>.filter fun i => u < s n i).card : ℝ) ≤
      H*u^(-(4:ℝ)/3))
    (hpartition : ∀ n, L ≤ ∑ i ∈ S n, lam n i) : L = 0 := by
  classical
  by_contra hne
  have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm hne)
  have hdecay : Tendsto (fun M : ℝ => H*M^(-(4:ℝ)/3)) atTop (𝓝 0) := by
    simpa only [neg_div,mul_zero] using
      (tendsto_rpow_neg_atTop (show (0:ℝ)<4/3 by norm_num)).const_mul H
  obtain ⟨M,hM,hMH⟩ : ∃ M : ℝ, 0 < M ∧ H*M^(-(4:ℝ)/3) < L/2 := by
    have hev := (hdecay.eventually (eventually_lt_nhds (half_pos hLp))).and
      (eventually_gt_atTop (0:ℝ))
    obtain ⟨M,h1,h2⟩ := hev.exists
    exact ⟨M,h2,h1⟩
  have hμsum (n : ℕ) : ∑ i ∈ S n, μ n i ≤
      2*B₀+B*(q n)^(1-α)*T^α :=
    activity_sum_bound (S n) (μ n) (b n) (θ n) (hq n).le hB hT
      (by linarith) hα1 (hcard n) (hbsum n) (hθ0 n) (hθsum n) (hactivity n)
  have hdecay2 := low_bound_tendsto_zero hq hqtop hα A M B₀ B T
  have hthr : 0 < (L/2)^3 := pow_pos (half_pos hLp) _
  obtain ⟨n,hn⟩ := (hdecay2.eventually (eventually_lt_nhds hthr)).exists
  have hhigh := high_mass_bound (S n) (lam n) (s n) (hq n) hM (hlam1 n) (htail n)
  have hlow := low_cube_bound (S n) (lam n) (μ n) (s n) (hq n) hM hA
    (hcard n) (hlam0 n) (hμ0 n) (hs0 n) (hmass n) (hμsum n)
  have hlow' : (∑ i ∈ S n with s n i ≤ M*(q n)^(-(3:ℝ)/4), lam n i) < L/2 := by
    by_contra hnot
    have hlole : L/2 ≤ ∑ i ∈ S n with s n i ≤ M*(q n)^(-(3:ℝ)/4), lam n i := le_of_not_gt hnot
    have hp := pow_le_pow_left₀ (half_pos hLp).le hlole 3
    exact (not_lt_of_ge (hp.trans hlow)) hn
  have hsplit := Finset.sum_filter_add_sum_filter_not (S n)
    (fun i => s n i ≤ M*(q n)^(-(3:ℝ)/4)) (lam n)
  simp only [not_le] at hsplit
  have htotal := hpartition n
  linarith only [hhigh,hMH,hlow',hsplit,htotal]

end PlanarHalving.Boundary

namespace PlanarHalving.RankCoordinates
open Set

lemma exists_slope_avoiding (p : Point) (F : Finset Point) {l u : ℝ}
    (hlu : l < u) (hp : p ∉ F) :
    ∃ s ∈ Ioo l u, ∀ z ∈ F, z.2 ≠ p.2+s*(z.1-p.1) := by
  classical
  obtain ⟨s,hs,havoid⟩ := (Ioo_infinite hlu).exists_notMem_finset
    (F.image (fun z => (z.2-p.2)/(z.1-p.1)))
  refine ⟨s,hs,?_⟩
  intro z hz he
  by_cases hx : z.1 = p.1
  · have heq : z = p := Prod.ext hx (by rw [hx,sub_self,mul_zero,add_zero] at he; exact he)
    exact hp (heq ▸ hz)
  · apply havoid
    apply Finset.mem_image.mpr
    refine ⟨z,hz,?_⟩
    apply (div_eq_iff (sub_ne_zero.mpr hx)).mpr
    linarith only [he]

lemma exists_affine_avoiding (F : Finset Point) (s : ℝ) :
    ∃ c : ℝ, ∀ z ∈ F, s*z.1+c ≠ z.2 := by
  classical
  obtain ⟨c,_,hc⟩ := (Set.infinite_univ : (Set.univ : Set ℝ).Infinite).exists_notMem_finset
    (F.image (fun z => z.2-s*z.1))
  refine ⟨c,?_⟩
  intro z hz he
  apply hc
  exact Finset.mem_image.mpr ⟨z,hz,by linarith only [he]⟩

end PlanarHalving.RankCoordinates

namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates
variable {R : ℕ}

lemma ConvexPath.interior_slopes (C : ConvexPath R) {L U : ℝ}
    (hLU : L < U)
    (hedge : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      L < slope (C.point b.castSucc) (C.point b.succ) ∧
      slope (C.point b.castSucc) (C.point b.succ) < U) :
    ∃ l u : ℝ, L < l ∧ l ≤ u ∧ u < U ∧
      ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
        l < slope (C.point b.castSucc) (C.point b.succ) ∧
        slope (C.point b.castSucc) (C.point b.succ) < u := by
  classical
  let E := Finset.univ.filter (fun b : Fin R => C.point b.castSucc ≠ C.point b.succ)
  by_cases he : E.Nonempty
  · obtain ⟨b,hb,hbmin⟩ := Finset.exists_min_image E
      (fun b => slope (C.point b.castSucc) (C.point b.succ)) he
    obtain ⟨c,hc,hcmax⟩ := Finset.exists_max_image E
      (fun b => slope (C.point b.castSucc) (C.point b.succ)) he
    have hb' := (Finset.mem_filter.mp hb).2
    have hc' := (Finset.mem_filter.mp hc).2
    obtain ⟨l,hlL,hl⟩ := exists_between (hedge b hb').1
    obtain ⟨u,hu,huU⟩ := exists_between (hedge c hc').2
    refine ⟨l,u,hlL,((hl.trans_le (hbmin c hc)).trans hu).le,huU,?_⟩
    intro i hi
    have hi' : i ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩
    exact ⟨hl.trans_le (hbmin i hi'),(hcmax i hi').trans_lt hu⟩
  · obtain ⟨l,hlL,hlU⟩ := exists_between hLU
    refine ⟨l,l,hlL,le_rfl,hlU,?_⟩
    intro b hb
    exact (he ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩⟩).elim

lemma ConvexPath.exists_clean_extension (C : ConvexPath R) (F : Finset Point)
    {L U : ℝ} (hLU : L < U)
    (hp₀ : C.point 0 ∉ F) (hp₁ : C.point (Fin.last R) ∉ F)
    (hedge : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      L < slope (C.point b.castSucc) (C.point b.succ) ∧
      slope (C.point b.castSucc) (C.point b.succ) < U) :
    ∃ l u : ℝ, L < l ∧ l ≤ u ∧ u < U ∧
      (∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
        l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧
        slope (C.point b.castSucc) (C.point b.succ) ≤ u) ∧
      ∀ z ∈ F, C.extension l u z.1 = z.2 →
        ∃ b : Fin R, C.point b.castSucc ≠ C.point b.succ ∧
          z ∈ segment ℝ (C.point b.castSucc) (C.point b.succ) := by
  obtain ⟨l₀,u₀,hl₀,hlu₀,hu₀,hs₀⟩ := C.interior_slopes hLU hedge
  obtain ⟨l,hl,hlavoid⟩ := exists_slope_avoiding (C.point 0) F hl₀ hp₀
  obtain ⟨u,hu,huavoid⟩ := exists_slope_avoiding (C.point (Fin.last R)) F hu₀ hp₁
  have hlu : l ≤ u := ((hl.2.trans_le hlu₀).trans hu.1).le
  have hs (b : Fin R) (hb : C.point b.castSucc ≠ C.point b.succ) :
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧
      slope (C.point b.castSucc) (C.point b.succ) ≤ u :=
    ⟨(hl.2.trans (hs₀ b hb).1).le,((hs₀ b hb).2.trans hu.1).le⟩
  refine ⟨l,u,hl.1,hlu,hu.2,hs,?_⟩
  intro z hz hgraph
  rcases C.extension_cases hlu hs hgraph with hleft | hright | hmiddle
  · exact (hlavoid z hz hleft.2).elim
  · exact (huavoid z hz hright.2).elim
  · exact hmiddle

end PlanarHalving.Batches

namespace PlanarHalving.RankCoordinates
open Set

noncomputable def slot {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ) (p : Point) : ℕ :=
  (Finset.univ.filter (fun i => g i p.1 < p.2)).card

lemma slot_lt_of_le_imp_lt {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ)
    {p q : Point} (h : ∀ i, g i p.1 ≤ p.2 → g i q.1 < q.2)
    (hp : ∃ i, g i p.1 = p.2) : slot g p < slot g q := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h i (Finset.mem_filter.mp hi).2.le⟩
  · obtain ⟨i,hi⟩ := hp
    intro he
    have hiq : i ∈ Finset.univ.filter (fun i => g i q.1 < q.2) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,h i hi.le⟩
    rw [← he] at hiq
    exact (lt_irrefl (p.2)) (hi ▸ (Finset.mem_filter.mp hiq).2)

lemma slot_chord_bounds {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ)
    {l u : ℝ}
    (hs : ∀ i x y, x ≤ y → l*(y-x) ≤ g i y-g i x ∧ g i y-g i x ≤ u*(y-x))
    {p q : Point} (hx : p.1 ≤ q.1) (hp : ∃ i, g i p.1 = p.2)
    (hq : ∃ i, g i q.1 = q.2) (he : slot g p = slot g q) :
    l*(q.1-p.1) ≤ q.2-p.2 ∧ q.2-p.2 ≤ u*(q.1-p.1) := by
  constructor
  · by_contra hn
    have ht := slot_lt_of_le_imp_lt g (p := q) (q := p) (fun i hi => by
      have hh := (hs i p.1 q.1 hx).1
      linarith only [hh,hi,lt_of_not_ge hn]) hq
    exact (ne_of_lt ht) he.symm
  · by_contra hn
    have ht := slot_lt_of_le_imp_lt g (p := p) (q := q) (fun i hi => by
      have hh := (hs i p.1 q.1 hx).2
      linarith only [hh,hi,lt_of_not_ge hn]) hp
    exact (ne_of_lt ht) he

theorem pair_slots_injOn {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ι → ℝ → ℝ) (h : κ → ℝ → ℝ) {l u l' u' : ℝ}
    (hg : ∀ i x y, x ≤ y → l*(y-x) ≤ g i y-g i x ∧ g i y-g i x ≤ u*(y-x))
    (hh : ∀ i x y, x ≤ y → l'*(y-x) ≤ h i y-h i x ∧ h i y-h i x ≤ u'*(y-x))
    (hgap : u < l') (S : Set Point)
    (hS : ∀ p ∈ S, (∃ i, g i p.1 = p.2) ∧ ∃ j, h j p.1 = p.2) :
    Set.InjOn (fun p => (slot g p,slot h p)) S := by
  have horder {p q : Point} (hp : p ∈ S) (hq : q ∈ S)
      (he : (slot g p,slot h p) = (slot g q,slot h q)) : ¬ p.1 < q.1 := by
    intro hx
    have hg' := (slot_chord_bounds g hg hx.le (hS p hp).1 (hS q hq).1 (congrArg Prod.fst he)).2
    have hh' := (slot_chord_bounds h hh hx.le (hS p hp).2 (hS q hq).2 (congrArg Prod.snd he)).1
    have hstrict := mul_lt_mul_of_pos_right hgap (sub_pos.mpr hx)
    linarith only [hg',hh',hstrict]
  intro p hp q hq he
  have hx : p.1 = q.1 := le_antisymm (le_of_not_gt (horder hq hp he.symm)) (le_of_not_gt (horder hp hq he))
  have hy := slot_chord_bounds g hg hx.le (hS p hp).1 (hS q hq).1 (congrArg Prod.fst he)
  rw [hx,sub_self,mul_zero,mul_zero] at hy
  exact Prod.ext hx (by linarith only [hy.1,hy.2])

lemma slot_lt_card {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ) {p : Point}
    (hp : ∃ i, g i p.1 = p.2) : slot g p < Fintype.card ι := by
  classical
  apply lt_of_lt_of_eq (Finset.card_lt_card ?_) (Finset.card_univ : _ = Fintype.card ι)
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset ..,?_⟩
  obtain ⟨i,hi⟩ := hp
  intro he
  have hmem := Finset.mem_univ i
  rw [← he] at hmem
  exact (lt_irrefl (p.2)) (hi ▸ (Finset.mem_filter.mp hmem).2)

end PlanarHalving.RankCoordinates

end OAI
