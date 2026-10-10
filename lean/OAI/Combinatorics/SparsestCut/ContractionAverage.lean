import OAI.Combinatorics.SparsestCut.CubeTransfer

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceContraction
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts SourceMetric
noncomputable section
variable {m : ℕ}
local notation "d" => (m+1:ℕ)
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "μ" => (CubePoincare.cube (m:=d))
lemma integral_bound (f : PivotFamily.PFamily d) (hm : 3000 ≤ d) (hl : 1≤Real.log d) (hH : H ≤ d)
    (Z : V f → EuclideanSpace ℝ (V f))
    (hmac : ∀ v w, |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt d*
         ‖B f (NeZero.pos d) v.val.1 (RoundedCharts.coordinate (u f) (p d 2000) v)-
           B f (NeZero.pos d) w.val.1 (RoundedCharts.coordinate (u f) (p d 2000) w)‖|≤err (m:=d)+8*p d 8)
    (hlocal : ∀ v w, v.val.1=w.val.1 → (∑ i, |RoundedCharts.coordinate (u f) (p d 2000) v i-
        RoundedCharts.coordinate (u f) (p d 2000) w i|)=p d 2000 →
        ‖Z v-Z w‖^2≤50000000*p d 2000*p d 5*(Real.log d)^2)
    {A : Type u1} [Fintype A] (F : V f → A → ℝ)
    (hcon : ∀ v w, (∑ a, |F v a-F w a|)≤‖Z v-Z w‖^2)
    (s0 : Fin (d^3)) :
    (∫ z : E × E, ∑ a, |ConcreteCells.function (u f) (fun s i =>
        abs_pos.mp ((show 0<1/((d:ℝ)^30*Real.sqrt d) by positivity).trans
          (u_pivot f (Nat.succ_pos m) s i 0))) (p d 2000) F s0 a z.1-
        ConcreteCells.function (u f) (fun s i =>
        abs_pos.mp ((show 0<1/((d:ℝ)^30*Real.sqrt d) by positivity).trans
          (u_pivot f (Nat.succ_pos m) s i 0))) (p d 2000) F s0 a z.2| ∂(μ).prod μ)≤C*weight d := by
  classical
  have hm0 := Nat.succ_pos m
  have hm1 : 1 ≤ d := by omega
  have hx : (1:ℝ) ≤ d := by exact_mod_cast hm1
  have hx0 : (0:ℝ)<d := by exact_mod_cast hm0
  have hu0 : ∀ s i, u f s i 0≠0 := by
    intro s i h
    have hh := u_pivot f hm0 s i 0
    rw [h,abs_zero] at hh
    have hp : 0<1/((d:ℝ)^30*Real.sqrt d) := by positivity
    linarith
  have hτ := p_pos hx0 2000
  have hlam := p_pos hx0 2
  have hlam1 : p d 2<1 := by
    unfold p
    apply (div_lt_one (by positivity)).mpr
    have hh : (2:ℝ) ≤ d := by exact_mod_cast (show 2 ≤ d by omega)
    nlinarith only [hh]
  let M : ℝ := ∑ v : V f, ∑ a, |F v a|
  have hM : 0≤M := Finset.sum_nonneg (fun v _ => Finset.sum_nonneg (fun a _ => abs_nonneg _))
  have hbound (v : V f) (a : A) : |F v a|≤M := by
    exact (Finset.single_le_sum (fun a _ => abs_nonneg (F v a)) (Finset.mem_univ a)).trans
      (Finset.single_le_sum (fun v _ => Finset.sum_nonneg (fun a _ => abs_nonneg (F v a))) (Finset.mem_univ v))
  have hclose : ∀ s t x (hx : x∈RoundedCharts.cube 2)
      (hs : RoundedCharts.regular (u f s) (p d 2000) x) (ht : RoundedCharts.regular (u f t) (p d 2000) x),
      (∑ a, |F (ContractionCore.vertex (u f) (p d 2000) s x hx hs) a-
        F (ContractionCore.vertex (u f) (p d 2000) t x hx ht) a|)≤C₀*p d 8 := by
    intro s t x hx hs ht
    have hh := (abs_le.mp (macro_bound f hm Z hmac s t x x hx hx hs ht)).2
    simp only [sub_self,norm_zero,mul_zero,sub_zero] at hh
    exact (hcon _ _).trans hh
  have hmacro : ∀ s x y (hx : x∈RoundedCharts.cube 2) (hy : y∈RoundedCharts.cube 2)
      (hs : RoundedCharts.regular (u f s) (p d 2000) x) (ht : RoundedCharts.regular (u f s) (p d 2000) y),
      (∑ a, |F (ContractionCore.vertex (u f) (p d 2000) s x hx hs) a-
        F (ContractionCore.vertex (u f) (p d 2000) s y hy ht) a|)≤KernelApprox.cstar*Real.sqrt d*‖x-y‖+C₀*p d 8 := by
    intro s x y hx hy hs ht
    have hh := (abs_le.mp (macro_bound f hm Z hmac s s x y hx hy hs ht)).2
    exact (hcon _ _).trans (by simpa only [ContractionCore.vertex,SourceMetric.vertex,add_comm] using (sub_le_iff_le_add.mp hh))
  have hjump : ∀ (vp vm : V f) (i : Fin (d^6)), vp.val.1=vm.val.1 → vp.val.2 i=vm.val.2 i+1 →
      (∀ j, j≠i → vp.val.2 j=vm.val.2 j) → (∑ a, |F vp a-F vm a|)≤50000000*p d 2000*p d 5*(Real.log d)^2 := by
    intro vp vm i hc hi hj
    exact (hcon vp vm).trans (hlocal vp vm hc (one_step f vp vm i hi hj))
  have h := ContractionAverage.average (u f) hu0 (u_nonparallel f hm0) (fun s i => (u_norm f hm0 s i).2)
    hτ hlam hlam1 (by positivity : 0≤11*Real.sqrt (Real.log d)/Real.sqrt d)
    (by unfold p; positivity : 0≤50000000*p d 2000*p d 5*(Real.log d)^2)
    (mul_nonneg KernelApprox.cstar_pos.le (Real.sqrt_nonneg _))
    F hM hbound hclose hmacro hjump (fun s i => small f hm1 hH s i 0) (good_dual f hm0) s0
  exact h.trans (contraction_numeric hm1 hl)
end
end UniformSparsestCut.SourceContraction

end

end OAI
