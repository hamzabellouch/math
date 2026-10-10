import OAI.Analysis.DiamondDistortion.PathLenses

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace Midpoint
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Packing with one finite-rank head and a common tail bound; no head norm
    estimate and no attained infinite minimum is used. -/
lemma tail_packing (P : X →L[ℝ] X) [FiniteDimensional ℝ (LinearMap.range P.toLinearMap)]
    (z : ℕ → X) {R ε T : ℝ} (hz : ∀ i,‖z i‖ ≤ R)
    (hs : ∀ i j,i ≠ j → ε ≤ ‖z i-z j‖) (ht : ∀ i,‖z i-P (z i)‖ ≤ T) :
    ε/2 ≤ T := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨i,j,hij,hP⟩ := finite_rank_pair P z hz hη
  let w := (1/2:ℝ) • (z i-z j)
  have hw : ε/2 ≤ ‖w‖ := by
    dsimp [w]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    linarith [hs i j hij]
  have he : w=P w+(1/2:ℝ) • ((z i-P (z i))-(z j-P (z j))) := by
    dsimp [w]
    rw [map_smul,map_sub]
    module
  have htail : ‖(1/2:ℝ) • ((z i-P (z i))-(z j-P (z j)))‖ ≤ T := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hh := (norm_sub_le (z i-P (z i)) (z j-P (z j))).trans (add_le_add (ht i) (ht j))
    linarith
  have hnorm := norm_add_le (P w) ((1/2:ℝ) • ((z i-P (z i))-(z j-P (z j))))
  rw [← he] at hnorm
  change ‖P w‖ < η at hP
  linarith

end Midpoint

namespace PathApplications
open Midpoint
variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Threshold-removal uses a single head for *all* deviations at this radius. -/
def RelativeInput (A : Heads ι X) : Prop :=
  ∀ (x : X),x ≠ 0 → ∀ δ : ℝ,0 < δ → δ ≤ 1 → ∃ H : ι,
    ∀ y : X,‖x+y‖ ≤ (1+δ)*‖x‖ → ‖x-y‖ ≤ (1+δ)*‖x‖ →
      ‖y-A.projection H y‖ ≤ 72*Real.sqrt δ*‖x‖

def relativeDelta (D : ℝ) : ℝ := ((200*D)⁻¹)^2

lemma relative_parameters {D : ℝ} (hD : 1 ≤ D) :
    0 < relativeDelta D ∧ relativeDelta D ≤ 1 ∧ 72*Real.sqrt (relativeDelta D)*D < 1 := by
  have hDpos : 0 < D := by linarith
  have hinv : 0 < (200*D)⁻¹ := by positivity
  have hinv1 : (200*D)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr (by linarith)
  have hsqrt : Real.sqrt (relativeDelta D)=(200*D)⁻¹ := by
    unfold relativeDelta
    exact Real.sqrt_sq hinv.le
  refine ⟨by unfold relativeDelta; positivity,by unfold relativeDelta; nlinarith,?_⟩
  rw [hsqrt]
  have he : 72*(200*D)⁻¹*D=72/200 := by field_simp
  rw [he]
  norm_num

lemma relative_lens_impossible (A : Heads ι X) (hinput : RelativeInput A)
    {D : ℝ} (hD : 1 ≤ D) {x : X} (z : ℕ → X) (hx : 1 ≤ ‖x‖) (hxD : ‖x‖ ≤ D)
    (hp : ∀ i,‖x+z i‖ ≤ (1+relativeDelta D)*‖x‖)
    (hm : ∀ i,‖x-z i‖ ≤ (1+relativeDelta D)*‖x‖)
    (hs : ∀ i j,i ≠ j → 2 ≤ ‖z i-z j‖) : False := by
  obtain ⟨hδ,hδ1,hδD⟩ := relative_parameters hD
  have hx0 : x ≠ 0 := by intro h; simp only [h,norm_zero] at hx; linarith
  obtain ⟨H,hH⟩ := hinput x hx0 (relativeDelta D) hδ hδ1
  let := A.finite H
  have hh := tail_packing (A.projection H) z (fun i => Diamond.norm_deviation_le (hp i) (hm i))
    hs (fun i => hH (z i) (hp i) (hm i))
  have hm := mul_le_mul_of_nonneg_left hxD (show 0 ≤ 72*Real.sqrt (relativeDelta D) by positivity)
  linarith

/-- An actual original child exceeds the relative factor, rather than merely
    a quotient representative or a supremum satisfying a non-strict bound. -/
lemma relative_actual_child (A : Heads ι X) (hinput : RelativeInput A)
    {D : ℝ} (hD : 1 ≤ D) {x : X} (z : ℕ → X) (hx : 1 ≤ ‖x‖) (hxD : ‖x‖ ≤ D)
    (hs : ∀ i j,i ≠ j → 2 ≤ ‖z i-z j‖) :
    ∃ i,(1+relativeDelta D)*‖x‖ < max ‖x+z i‖ ‖x-z i‖ := by
  by_contra! hn
  exact relative_lens_impossible A hinput hD z hx hxD
    (fun i => (le_max_left _ _).trans (hn i)) (fun i => (le_max_right _ _).trans (hn i)) hs

theorem relative_cost (A : Heads ι X) (hinput : RelativeInput A)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    (1+relativeDelta D)^k ≤ D := by
  obtain ⟨hδ,hδ1,hδD⟩ := relative_parameters hf.1
  have hb : 0 < 1+relativeDelta D := by positivity
  let c : ℝ := 1/(1+relativeDelta D)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := (div_le_one₀ hb).mpr (by linarith)
  have hstep : ∀ (x : X) (z : ℕ → X) (R : ℝ),0 ≤ R → R ≤ D → 1 ≤ ‖x‖ →
      (∀ i,‖x+z i‖ ≤ R) → (∀ i,‖x-z i‖ ≤ R) →
      (∀ i j,i ≠ j → 2*1 ≤ ‖z i-z j‖) → ‖x‖ ≤ c*R := by
    intro x z R hR hRD hx hp hm hs
    have hxD := (Diamond.norm_center_le (hp 0) (hm 0)).trans hRD
    obtain ⟨i,hi⟩ := relative_actual_child A hinput hf.1 z hx hxD (by simpa using hs)
    have hh := hi.trans_le (max_le (hp i) (hm i))
    have hnorm : ‖x‖ ≤ R/(1+relativeDelta D) := (le_div_iff₀ hb).mpr (by nlinarith)
    simpa only [c,div_eq_mul_inv,one_mul,mul_comm] using hnorm
  obtain ⟨_,_,hnorm⟩ := Diamond.normalized_distortion f hf
  have hh := Diamond.iterate_contraction hc hc1 hstep k (fun v => s⁻¹ • f v)
    (show 0 ≤ D by linarith [hf.1]) le_rfl (fun u v => (hnorm u v).1)
    (fun e => Diamond.slope_upper _ (fun u v => by simpa using (hnorm u v).2) e)
  have he : c^k*D=D/(1+relativeDelta D)^k := by dsimp [c]; rw [div_pow,one_pow]; ring
  rw [he] at hh
  exact (one_le_div (by positivity : 0 < (1+relativeDelta D)^k)).mp hh

end PathApplications

namespace Midpoint
open Filter
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace.SeparableSpace (StrongDual ℝ X)]
lemma bounded_scalar_subsequence (z : ℕ → X) {R : ℝ} (hz : ∀ i,‖z i‖ ≤ R) :
    ∃ n : ℕ → ℕ,StrictMono n ∧ ∀ f : StrongDual ℝ X,∃ a : ℝ,
      Tendsto (fun i => f (z (n i))) atTop (𝓝 a) := by
  let w (i : ℕ) : WeakDual ℝ (StrongDual ℝ X) :=
    StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual ℝ X (z i))
  have hw : ∀ i,w i ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R := by
    intro i
    change dist (NormedSpace.inclusionInDoubleDual ℝ X (z i)) 0 ≤ R
    convert (NormedSpace.double_dual_bound ℝ X (z i)).trans (hz i) using 1
    exact @dist_zero_right (StrongDual ℝ (StrongDual ℝ X)) inferInstance
      (NormedSpace.inclusionInDoubleDual ℝ X (z i))
  obtain ⟨a,ha,n,hn,ht⟩ := WeakDual.isSeqCompact_closedBall ℝ (StrongDual ℝ X) 0 R hw
  refine ⟨n,hn,fun f => ⟨a f,?_⟩⟩
  have hh := ((WeakDual.eval_continuous f).tendsto a).comp ht
  exact hh

lemma bounded_weak_pair (z : ℕ → X) {R : ℝ} (hz : ∀ i,‖z i‖ ≤ R) :
    ∃ n : ℕ → ℕ,StrictMono n ∧ ∀ f : StrongDual ℝ X,
      Tendsto (fun i => f ((1/2:ℝ) • (z (n (2*i))-z (n (2*i+1))))) atTop (𝓝 0) := by
  obtain ⟨n,hn,hf⟩ := bounded_scalar_subsequence z hz
  refine ⟨n,hn,fun f => ?_⟩
  obtain ⟨a,ha⟩ := hf f
  have ht0 : Tendsto (fun i : ℕ => 2*i) atTop atTop := tendsto_atTop_mono (by intro i; dsimp only [id]; omega) tendsto_id
  have ht1 : Tendsto (fun i : ℕ => 2*i+1) atTop atTop := tendsto_atTop_mono (by intro i; dsimp only [id]; omega) tendsto_id
  have hh := ((ha.comp ht0).sub (ha.comp ht1)).const_mul (1/2:ℝ)
  simpa only [Function.comp_def,sub_self,mul_zero,map_smul,map_sub,smul_eq_mul] using hh
end Midpoint

namespace PathApplications
open Midpoint Filter
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def WeakInput (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∀ (x : X) (y : ℕ → X),(∃ M : ℝ,∀ j,‖y j‖ ≤ M) → WeaklyNull y →
    Real.sqrt (‖x‖^2+(1/16:ℝ)*(liminf (fun j => ‖y j‖) atTop)^2) ≤
      liminf (fun j => max ‖x+y j‖ ‖x-y j‖) atTop

lemma weak_lens [TopologicalSpace.SeparableSpace (StrongDual ℝ X)] (hinput : WeakInput X) :
    Diamond.SquareLens X (1/64) := by
  intro x z R ε hR hε hp hm hs
  obtain ⟨n,hn,hweak⟩ := Midpoint.bounded_weak_pair z (fun i => Diamond.norm_deviation_le (hp i) (hm i))
  let y (i : ℕ) := (1/2:ℝ) • (z (n (2*i))-z (n (2*i+1)))
  have hnull : WeaklyNull y := hweak
  have hend (i : ℕ) : ‖x+y i‖ ≤ R ∧ ‖x-y i‖ ≤ R := average_lens z hp hm _ _
  have hyR (i : ℕ) : ‖y i‖ ≤ R := Diamond.norm_deviation_le (hend i).1 (hend i).2
  have hyl (i : ℕ) : ε/2 ≤ ‖y i‖ := by
    have hij : n (2*i) ≠ n (2*i+1) := hn.injective.ne (by omega)
    dsimp [y]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    linarith [hs _ _ hij]
  have hlim : ε/2 ≤ liminf (fun i => ‖y i‖) atTop :=
    le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hyR) (Eventually.of_forall hyl)
  have hmaxL (i : ℕ) : 0 ≤ max ‖x+y i‖ ‖x-y i‖ := (norm_nonneg _).trans (le_max_left _ _)
  have hmaxR (i : ℕ) : max ‖x+y i‖ ‖x-y i‖ ≤ R := max_le (hend i).1 (hend i).2
  have hlimR : liminf (fun i => max ‖x+y i‖ ‖x-y i‖) atTop ≤ R :=
    liminf_le_of_frequently_le (Eventually.of_forall hmaxR).frequently
      (isBoundedUnder_of_eventually_ge (Eventually.of_forall hmaxL))
  have hh := (hinput x y ⟨R,hyR⟩ hnull).trans hlimR
  have hsq : ‖x‖^2+(1/16:ℝ)*(liminf (fun i => ‖y i‖) atTop)^2 ≤ R^2 := by
    exact (Real.sqrt_le_iff).mp hh |>.2
  have hlim0 : 0 ≤ liminf (fun i => ‖y i‖) atTop := (by positivity : 0 ≤ ε/2).trans hlim
  have hl2 := (sq_le_sq₀ (by positivity : 0 ≤ ε/2) hlim0).mpr hlim
  nlinarith

theorem weak_linear [TopologicalSpace.SeparableSpace (StrongDual ℝ X)] (hinput : WeakInput X)
    {D s : ℝ} (k : ℕ) (f : Diamond.Vertex k → X) (hf : Diamond.HasDistortion k f D s) :
    1+(k:ℝ)/64 ≤ D^2 := by
  have hh := Diamond.squared_transfer (by norm_num : (0:ℝ)<1/64) (weak_lens hinput) k f D s hf
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  linarith

end PathApplications

end DiamondDistortion

end

end OAI
