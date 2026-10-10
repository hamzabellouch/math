import Mathlib
import OAI.Analysis.SymmetricDomains.FiniteNashCoverVertical

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

theorem local_real_hom_nat_mul {G : Type*} [Group G] (g : ℝ → G) (h0 : g 0=1)
    {ε : ℝ} (hε : 0<ε)
    (hm : ∀ s t : ℝ, |s|<ε → |t|<ε → g (s+t)=g s*g t)
    (n : ℕ) (u : ℝ) (hu : |(n:ℝ)*u|<ε) : g ((n:ℝ)*u)=g u^n := by
  by_cases hn : n=0
  · simp [hn,h0]
  have hnu : |(n:ℝ)*u|=(n:ℝ)*|u| := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
  have hun : |u|<ε := by
    have hn1 : (1:ℝ)≤n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn)
    rw [hnu] at hu
    nlinarith [abs_nonneg u]
  have hh : ∀ j : ℕ, j≤n → g ((j:ℝ)*u)=g u^j := by
    intro j hj
    induction j with
    | zero => simp [h0]
    | succ j ih =>
      have hjn : j≤n := (Nat.le_succ j).trans hj
      have hju : |(j:ℝ)*u|<ε := by
        rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg j)]
        rw [hnu] at hu
        have hc : (j:ℝ)≤n := Nat.cast_le.mpr hjn
        nlinarith [abs_nonneg u]
      rw [Nat.cast_succ,add_mul,one_mul,hm _ _ hju hun,ih hjn,pow_succ]
  exact hh n le_rfl

theorem local_real_hom_subdivision_independent {G : Type*} [Group G]
    (g : ℝ → G) (h0 : g 0=1) {ε : ℝ} (hε : 0<ε)
    (hm : ∀ s t : ℝ, |s|<ε → |t|<ε → g (s+t)=g s*g t)
    (t : ℝ) {n m : ℕ} (hn : 0<n) (hms : 0 < m)
    (htn : |t/n|<ε) (htm : |t/m|<ε) : g (t/n)^n=g (t/m)^m := by
  have hnr : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hmr : (m:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hms)
  let u : ℝ := t/((n:ℝ)*m)
  have hen : (m:ℝ)*u=t/n := by
    dsimp [u]
    field_simp [hnr,hmr]
  have hem : (n:ℝ)*u=t/m := by
    dsimp [u]
    field_simp [hnr,hmr]
  have hgn := local_real_hom_nat_mul g h0 hε hm m u (by simpa only [hen] using htn)
  have hgm := local_real_hom_nat_mul g h0 hε hm n u (by simpa only [hem] using htm)
  rw [hen] at hgn
  rw [hem] at hgm
  rw [hgn,hgm,← pow_mul,← pow_mul,Nat.mul_comm m n]

theorem local_real_hom_extension {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (g : ℝ → G) (h0 : g 0=1) (hc : ContinuousAt g 0) {ε : ℝ} (hε : 0<ε)
    (hm : ∀ s t : ℝ, |s|<ε → |t|<ε → g (s+t)=g s*g t) :
    ∃ H : ℝ → G, H 0=1 ∧ Continuous H ∧ (∀ s t, H (s+t)=H s*H t) ∧
      ∀ t, |t|<ε → H t=g t := by
  have hex (t : ℝ) : ∃ n : ℕ, 0<n ∧ |t/n|<ε := by
    obtain ⟨n,hn⟩ := exists_nat_gt (max 1 (|t|/ε))
    have hnn : (1:ℝ)<n := (le_max_left _ _).trans_lt hn
    have hpos : 0<n := Nat.cast_pos.mp (by linarith : (0:ℝ)<n)
    refine ⟨n,hpos,?_⟩
    rw [abs_div,abs_of_pos (show 0 < (n:ℝ) from Nat.cast_pos.mpr hpos)]
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hpos)).mpr
    have hs := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hn)
    nlinarith
  have hchoose := hex
  choose N hN using hchoose
  let H : ℝ → G := fun t => g (t/N t)^(N t)
  have hspec (t : ℝ) (n : ℕ) (hn : 0<n) (ht : |t/n|<ε) : H t=g (t/n)^n :=
    local_real_hom_subdivision_independent g h0 hε hm t (hN t).1 hn (hN t).2 ht
  have hlocal (t : ℝ) (ht : |t|<ε) : H t=g t := by
    simpa only [Nat.cast_one,div_one,pow_one] using hspec t 1 (by decide) (by simpa using ht)
  have hH0 : H 0=1 := (hlocal 0 (by simpa using hε)).trans h0
  have hadd (s t : ℝ) : H (s+t)=H s*H t := by
    obtain ⟨n,hn,hnt⟩ := hex (max |s| (max |t| |s+t|))
    have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr hn
    have hmax : 0 ≤ max |s| (max |t| |s+t|) := (abs_nonneg s).trans (le_max_left _ _)
    rw [abs_div,abs_of_nonneg hmax,abs_of_pos hnpos] at hnt
    have hs : |s/n|<ε := by
      rw [abs_div,abs_of_pos hnpos]
      exact (div_le_div_of_nonneg_right (le_max_left _ _) hnpos.le).trans_lt hnt
    have ht : |t/n|<ε := by
      rw [abs_div,abs_of_pos hnpos]
      exact (div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hnpos.le).trans_lt hnt
    have hst : |(s+t)/n|<ε := by
      rw [abs_div,abs_of_pos hnpos]
      exact (div_le_div_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hnpos.le).trans_lt hnt
    have hcom : Commute (g (s/n)) (g (t/n)) := by
      change g (s/n)*g (t/n)=g (t/n)*g (s/n)
      rw [← hm _ _ hs ht,← hm _ _ ht hs,add_comm]
    rw [hspec (s+t) n hn hst,hspec s n hn hs,hspec t n hn ht,add_div,hm _ _ hs ht]
    exact hcom.mul_pow n
  have hHc0 : ContinuousAt H 0 := hc.congr (show g=ᶠ[𝓝 0] H from by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hε] with t ht
    exact (hlocal t (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)).symm)
  have hHc : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have h0t : ContinuousAt H (t-t) := by simpa only [sub_self] using hHc0
    have hsub : ContinuousAt (fun s : ℝ => s-t) t := continuousAt_id.sub continuousAt_const
    have hh : ContinuousAt (fun s : ℝ => H t*H (s-t)) t := continuousAt_const.mul
      (h0t.comp (f := fun s : ℝ => s-t) hsub)
    have he : (fun s : ℝ => H t*H (s-t))=H := by
      funext s
      rw [← hadd]
      congr 1
      ring
    rwa [he] at hh
  exact ⟨H,hH0,hHc,hadd,hlocal⟩
end Release061

end

end OAI
