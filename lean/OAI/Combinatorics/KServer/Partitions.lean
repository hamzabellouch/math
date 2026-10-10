import Mathlib
import OAI.Combinatorics.KServer.Experiments
import OAI.Combinatorics.KServer.Potential
import OAI.Combinatorics.KServer.RankProportions

namespace OAI

noncomputable section
open scoped BigOperators
open Finset Set

namespace KServer.Pilot
open RankTracking PosteriorRanks
variable {Ω Y : Type*} [Fintype Ω] [Fintype Y] [MetricSpace Y]

/-- Exact filtering for a profile chosen from the old observation history.
The old compact minimizer is a single admissible competitor on each old fiber. -/
lemma filtered_potential (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (H H' : Ω → ℕ) (hr : ∀ ω ν, H' ω = H' ν → H ω = H ν)
    (T : Template) (r : ℝ) (f g : Ω → Y → ℝ)
    (hg : ∀ y, Adapted H (fun ω => g ω y)) :
    avg w (fun ω => potential T r (fun y => posterior w H' (fun ν => f ν y) ω) (g ω)) ≤
      avg w (fun ω => potential T r (fun y => posterior w H (fun ν => f ν y) ω) (g ω)) := by
  let z : Ω → Y → ℝ := fun ω =>
    minimizer T r (fun y => posterior w H (fun ν => f ν y) ω) (g ω)
  have hz ω : Feasible T r (z ω) := (minimizer_spec _ _ _ _).1
  have hza : ∀ y, Adapted H (fun ω => z ω y) := by
    intro y ω ν h
    have hμ : (fun y => posterior w H (fun ν => f ν y) ω) =
        (fun y => posterior w H (fun ν => f ν y) ν) := by
      funext y
      exact posterior_adapted w H (fun ν => f ν y) ω ν h
    have hg' : g ω = g ν := funext fun y => hg y ω ν h
    simp only [z, hμ, hg']
  have hc y : Adapted H (fun ω => integrand T r (g ω) (z ω) y) := by
    intro ω ν h
    have hg' : g ω = g ν := funext fun y => hg y ω ν h
    have hz' : z ω = z ν := funext fun y => hza y ω ν h
    dsimp only
    rw [hg', hz']
  calc
    _ ≤ avg w (fun ω => objective T r
        (fun y => posterior w H' (fun ν => f ν y) ω) (g ω) (z ω)) :=
      avg_mono hw fun ω => potential_le (hz ω)
    _ = avg w (fun ω => objective T r
        (fun y => posterior w H (fun ν => f ν y) ω) (g ω) (z ω)) := by
      simp only [objective, avg, mul_sum]
      rw [sum_comm, sum_comm (f := fun ω y =>
        w ω * (r * (posterior w H (fun ν => f ν y) ω * integrand T r (g ω) (z ω) y)))]
      apply sum_congr rfl
      intro y _
      have he := (weighted_posterior hw H' (fun ν => f ν y)
        (fun ω => integrand T r (g ω) (z ω) y)
        (fun ω ν h => hc y ω ν (hr ω ν h))).trans
        (weighted_posterior hw H (fun ν => f ν y)
          (fun ω => integrand T r (g ω) (z ω) y) (hc y)).symm
      have he' := congrArg (r * ·) he
      simpa only [avg, mul_sum, mul_assoc, mul_comm, mul_left_comm] using he'
    _ = _ := rfl

end KServer.Pilot

namespace KServer.FiniteExperiment
open RankTracking PosteriorRanks Pilot
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]
variable {k H : ℕ} [NeZero k]

omit [MetricSpace Y] in
lemma requestHistory_refines (t : ℕ) (σ ρ : Fin H → Y)
    (h : requestHistory (t+1) σ = requestHistory (t+1) ρ) :
    requestHistory t σ = requestHistory t ρ := by
  apply (requestHistory_eq_iff t σ ρ).mpr
  funext i
  have hh := congrFun ((requestHistory_eq_iff (t+1) σ ρ).mp h) i
  unfold requestPrefix at *
  by_cases hi : i.val < t
  · simpa [hi, show i.val < t+1 by omega] using hh
  · simp [hi]

/-- The precise signed filtering contribution of the actual hidden optimum. -/
lemma pilot_filtering (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Pilot.Template) (r : ℝ) (t : Fin H) (g : (Fin H → Y) → Y → ℝ)
    (hg : ∀ y, Adapted (requestHistory t.val) (fun σ => g σ y)) :
    avg law.val (fun σ => potential T r (muBefore s law t σ) (g σ)) ≤
      avg law.val (fun σ => potential T r (mu s law t.val σ) (g σ)) :=
  filtered_potential law.val law.property.1 (requestHistory t.val)
    (requestHistory (t.val+1)) (requestHistory_refines t.val) T r
    (fun σ => metricCount (hidden s σ t.val)) g hg

/-- Each realized physical update obeys the literal compact-pilot drift bound. -/
lemma pilot_physical (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Pilot.Template) {γ δ r₀ τ : ℝ} (t : Fin H) (σ : Fin H → Y)
    (g : ℕ → Y → ℝ) (n p : ℕ) (hσ : 0 < law.val σ)
    (hr : 0 < r₀) (hτ : 2 ≤ τ) (hγ0 : 0 < γ)
    (hγ : γ ≤ min (T.σ/64) (1/(1+T.L))) (hδ0 : 0 < δ) (hδ : δ ≤ 1/4112)
    (hpow : 100*T.R ≤ γ*(2:ℝ)^p)
    (hg : ∀ j<n, ∀ y, g j y ∈ Set.Icc 0 1)
    (hgLip : ∀ j<n, ∀ y z, |g j y-g j z| ≤ T.L*(dist y z/radius r₀ τ j)) :
    ∑ j ∈ range n, max (potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g j)-
      potential T (radius r₀ τ j) (muBefore s law t σ) (g j)) 0 ≤
        driftConstant T γ δ p*(1+Real.log ((k:ℝ)+1)) *
          ∑ y, nu s law t σ y * dist y (σ t) := by
  have he : mu s law (t.val+1) σ =
      moveMeasure (muBefore s law t σ) (nu s law t σ) (σ t) := by
    funext y
    simpa only [moveMeasure, eq_comm] using mu_move s law t σ hσ y
  rw [he]
  simpa only [moveCost, dist_comm] using pilot_drift (x := σ t) g n p hr hτ hγ0 hγ hδ0 hδ hpow
    (muBefore_nonneg s law t σ) (nu_nonneg s law t σ) (nu_le_muBefore s law t σ)
    (nu_total s law t σ hσ) (muBefore_total s law t σ hσ) hg hgLip

end KServer.FiniteExperiment

namespace KServer.FiniteExperiment
open RankTracking PosteriorRanks Pilot
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]
variable {k H : ℕ} [NeZero k]

/-- The actual expected physical pilot increments are paid entirely by OPT. -/
theorem pilot_physical_budget (s : Configuration k Y)
    (law : FiniteDistribution (Fin H → Y)) (T : Pilot.Template)
    {γ δ r₀ τ : ℝ} (g : Fin H → (Fin H → Y) → ℕ → Y → ℝ) (n p : ℕ)
    (hr : 0 < r₀) (hτ : 2 ≤ τ) (hγ0 : 0 < γ)
    (hγ : γ ≤ min (T.σ/64) (1/(1+T.L))) (hδ0 : 0 < δ) (hδ : δ ≤ 1/4112)
    (hpow : 100*T.R ≤ γ*(2:ℝ)^p)
    (hg : ∀ t σ j, j<n → ∀ y, g t σ j y ∈ Set.Icc 0 1)
    (hgLip : ∀ t σ j, j<n → ∀ y z,
      |g t σ j y-g t σ j z| ≤ T.L*(dist y z/radius r₀ τ j)) :
    (∑ t : Fin H, avg law.val (fun σ => ∑ j ∈ range n,
      max (potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g t σ j)-
        potential T (radius r₀ τ j) (muBefore s law t σ) (g t σ j)) 0)) ≤
      driftConstant T γ δ p * (1+Real.log ((k:ℝ)+1)) *
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ) := by
  calc
    _ ≤ ∑ t : Fin H, ∑ σ, law.val σ *
        (driftConstant T γ δ p * (1+Real.log ((k:ℝ)+1)) *
          ∑ y,nu s law t σ y*dist y (σ t)) := by
      apply sum_le_sum
      intro t _
      apply sum_le_sum
      intro σ _
      by_cases hσ : 0 < law.val σ
      · exact mul_le_mul_of_nonneg_left
          (pilot_physical s law T t σ (g t σ) n p hσ hr hτ hγ0 hγ hδ0 hδ hpow
            (hg t σ) (hgLip t σ)) (law.property.1 σ)
      · have hzero : law.val σ=0 := le_antisymm (le_of_not_gt hσ) (law.property.1 σ)
        simp [hzero]
    _ = _ := by
      simp only [mul_left_comm (law.val _) (driftConstant T γ δ p * (1+Real.log ((k:ℝ)+1))),
        ←mul_sum]
      rw [expected_moveCost]

/-- All-step signed filtering plus physical drift, before any decision to edit.
The edit charge is the literal difference of two achieved pilot minima. -/
theorem pilot_edit_budget (s : Configuration k Y)
    (law : FiniteDistribution (Fin H → Y)) (T : Pilot.Template)
    {γ δ r₀ τ : ℝ} (g : ℕ → (Fin H → Y) → ℕ → Y → ℝ) (n p : ℕ)
    (hr : 0 < r₀) (hτ : 2 ≤ τ) (hγ0 : 0 < γ)
    (hγ : γ ≤ min (T.σ/64) (1/(1+T.L))) (hδ0 : 0 < δ) (hδ : δ ≤ 1/4112)
    (hpow : 100*T.R ≤ γ*(2:ℝ)^p)
    (hg : ∀ t σ j, j<n → ∀ y, g t σ j y ∈ Set.Icc 0 1)
    (hgLip : ∀ t σ j, j<n → ∀ y z,
      |g t σ j y-g t σ j z| ≤ T.L*(dist y z/radius r₀ τ j))
    (hga : ∀ t j, j<n → ∀ y,
      Adapted (requestHistory t) (fun σ => g t σ j y)) :
    (∑ t : Fin H, avg law.val (fun σ => ∑ j ∈ range n,
      (potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g t.val σ j)-
        potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g (t.val+1) σ j)))) ≤
      driftConstant T γ δ p * (1+Real.log ((k:ℝ)+1)) *
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ) +
          ∑ j ∈ range n,2 * radius r₀ τ j * (k:ℝ) := by
  let V : ℕ → ℝ := fun t =>
    ∑ j ∈ range n,avg law.val (fun σ => potential T (radius r₀ τ j) (mu s law t σ) (g t σ j))
  let D : Fin H → ℝ := fun t => avg law.val (fun σ => ∑ j ∈ range n,
    max (potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g t.val σ j)-
      potential T (radius r₀ τ j) (muBefore s law t σ) (g t.val σ j)) 0)
  have hstep (t : Fin H) :
      avg law.val (fun σ => ∑ j ∈ range n,
        (potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g t.val σ j)-
          potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g (t.val+1) σ j))) ≤
        V t.val-V (t.val+1)+D t := by
    have hfilter := sum_le_sum (s := range n) fun j hj =>
      pilot_filtering s law T (radius r₀ τ j) t (fun σ => g t.val σ j)
        (hga t.val j (mem_range.mp hj))
    have hpoint := avg_mono law.property.1 (fun σ =>
      sum_le_sum (s := range n) fun j _ => le_max_left
        (potential T (radius r₀ τ j) (mu s law (t.val+1) σ) (g t.val σ j)-
         potential T (radius r₀ τ j) (muBefore s law t σ) (g t.val σ j)) 0)
    have avgsum (f : ℕ → (Fin H → Y) → ℝ) :
        avg law.val (fun σ => ∑ j ∈ range n,f j σ)=∑ j ∈ range n,avg law.val (f j) := by
      unfold avg
      simp only [mul_sum]
      rw [sum_comm]
    dsimp only [V,D] at *
    simp only [avgsum, avg_sub, sum_sub_distrib] at hpoint ⊢
    linarith
  have hVnonneg : 0 ≤ V H := by
    apply sum_nonneg
    intro j hj
    exact sum_nonneg fun σ _ => mul_nonneg (law.property.1 σ)
      (potential_bounds (radius_pos hr (by linarith) j).le (mu_nonneg s law H σ)
        (hg H σ j (mem_range.mp hj))).1
  have hVupper : V 0 ≤ ∑ j ∈ range n,2 * radius r₀ τ j * (k:ℝ) := by
    apply sum_le_sum
    intro j hj
    calc
      _ ≤ avg law.val (fun _ => 2 * radius r₀ τ j * (k:ℝ)) := by
        apply sum_le_sum
        intro σ _
        by_cases hσ : 0 < law.val σ
        · exact mul_le_mul_of_nonneg_left
            (by simpa only [mu_total s law 0 σ hσ] using
              (potential_bounds (radius_pos hr (by linarith) j).le (mu_nonneg s law 0 σ)
                (hg 0 σ j (mem_range.mp hj))).2) (law.property.1 σ)
        · have hz : law.val σ=0 := le_antisymm (le_of_not_gt hσ) (law.property.1 σ)
          simp [hz]
      _ = _ := avg_const _ law.property.2 _
  have hD := pilot_physical_budget s law T (fun t σ => g t.val σ) n p
    hr hτ hγ0 hγ hδ0 hδ hpow (fun t => hg t.val) (fun t => hgLip t.val)
  have hsum := sum_le_sum (s := (univ : Finset (Fin H))) (fun t _ => hstep t)
  have htelescope : (∑ t : Fin H,(V t.val-V (t.val+1)))=V 0-V H := by
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => V t-V (t+1)),Finset.sum_range_sub']
  rw [sum_add_distrib,htelescope] at hsum
  dsimp only [D] at hsum
  linarith

end KServer.FiniteExperiment

end


noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.HeavyCenters
open Pilot
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]

def template : Pilot.Template where
  σ := 1
  R := 512
  L := 1
  σ_pos := by norm_num
  σ_le := le_rfl
  R_ge := by norm_num
  L_nonneg := by norm_num

/-- The exact annulus charged at a heavy update. -/
def annulus (x : Y) (r : ℝ) : Finset Y :=
  univ.filter (fun p => 3*r<dist x p ∧ dist x p ≤ 120*r)

lemma annulus_bump_one {r : ℝ} (hr : 0<r) {x s p : Y}
    (hs : dist s x<r/4) (hp : p∈annulus x r) :
    Pilot.a template (dist s p/r)=1 := by
  have hp' := (mem_filter.mp hp).2
  have hlo : 1 ≤ dist s p/r := by
    apply (le_div_iff₀ hr).mpr
    have ht := dist_triangle x s p
    rw [dist_comm x s] at ht
    linarith
  have hhi : dist s p/r ≤ 512 := by
    apply (div_le_iff₀ hr).mpr
    have ht := dist_triangle s x p
    linarith
  simp only [Pilot.a,template,ite_eq_left hhi,one_pow,div_one]
  exact min_eq_right (by nlinarith)

omit [Fintype Y] in
lemma profile_weight_nonneg {r : ℝ} (hr : 0<r) (C : Finset Y) (x : Y)
    {z : Y → ℝ} (hz : ∀ i,0≤z i)
    (hmiddle : ∀ i,r/4 ≤ dist i x → dist i x ≤ 256*r → z i=0) (i : Y) :
    0 ≤ z i*(profile r C i-profile r (replace r C x) i) := by
  by_cases h : profile r (replace r C x) i ≤ profile r C i
  · exact mul_nonneg (hz i) (sub_nonneg.mpr h)
  · have hs := profile_increase_support hr C x i (lt_of_not_ge h)
    have hi : z i=0 := hmiddle i (by rw [dist_comm]; linarith)
      (by rw [dist_comm]; linarith)
    rw [hi,zero_mul]

lemma profile_residual_bound {r : ℝ} (hr : 0<r) (C : Finset Y) (x p : Y)
    {R : ℝ} (hR : R∈Set.Icc 0 1) :
    -(if p∈annulus x r then (1:ℝ) else 0) ≤
      (profile r C p-profile r (replace r C x) p)*R := by
  by_cases hp : p∈annulus x r
  · rw [ite_eq_left hp]
    have hm := mul_nonneg
      (show 0 ≤ profile r C p-profile r (replace r C x) p+1 by
        linarith [profile_nonneg r C p,profile_le_one r (replace r C x) p]) hR.1
    nlinarith [hR.2]
  · rw [ite_eq_right hp,neg_zero]
    apply mul_nonneg _ hR.1
    by_contra hn
    have hs := profile_increase_support hr C x p (by linarith)
    apply hp
    exact mem_filter.mpr ⟨mem_univ _,hs.1,by linarith [hs.2]⟩

/-- Pointwise objective decrease from the literal center replacement. -/
lemma edit_integrand_drop {r : ℝ} (hr : 0<r) (C : Finset Y) (x : Y)
    {z : Y → ℝ} (hz : Feasible template r z)
    (hfar : ∀ a∈C,8*r<dist a x)
    (hmiddle : ∀ i,r/4 ≤ dist i x → dist i x ≤ 256*r → z i=0)
    (hnear : ∃ s,dist s x<r/4 ∧ (1/2:ℝ) ≤ z s) (p : Y) :
    127*(if p∈annulus x r then (1:ℝ) else 0) ≤
      integrand template r (profile r C) z p-
        integrand template r (profile r (replace r C x)) z p := by
  obtain ⟨s,hs,hsz⟩ := hnear
  let R := 1-∑ i,z i*Pilot.b template (dist i p/r)
  have hR : R∈Set.Icc 0 1 := by
    constructor
    · exact sub_nonneg.mpr (sum_b_le_one hz p)
    · have hn := sum_nonneg (s := (univ : Finset Y))
        (fun i _ => mul_nonneg (hz.1 i) (Pilot.b_nonneg template (dist i p/r)))
      dsimp [R]
      linarith
  have hrb := profile_residual_bound hr C x p hR
  have he := near_profile_edit hr hfar hs
  have hsum : (∑ i,z i*(profile r C i-profile r (replace r C x) i)*
      Pilot.a template (dist i p/r)) ≥ (1/2:ℝ)*(if p∈annulus x r then (1:ℝ) else 0) := by
    by_cases hp : p∈annulus x r
    · rw [ite_eq_left hp,mul_one]
      have hb := single_le_sum (s := (univ : Finset Y))
        (fun i _ => mul_nonneg (profile_weight_nonneg hr C x hz.1 hmiddle i)
          (Pilot.a_nonneg template (dist i p/r))) (mem_univ s)
      rw [he.1,he.2,sub_zero,mul_one,annulus_bump_one hr hs hp,mul_one] at hb
      exact hsz.trans hb
    · rw [ite_eq_right hp,mul_zero]
      exact sum_nonneg fun i _ => mul_nonneg
        (profile_weight_nonneg hr C x hz.1 hmiddle i) (Pilot.a_nonneg template (dist i p/r))
  have hid : integrand template r (profile r C) z p-
      integrand template r (profile r (replace r C x)) z p =
      (profile r C p-profile r (replace r C x) p)*R+
      256*∑ i,z i*(profile r C i-profile r (replace r C x) i)*
        Pilot.a template (dist i p/r) := by
    have heq : (∑ i,z i*(1+profile r C i)*Pilot.a template (dist i p/r))-
      (∑ i,z i*(1+profile r (replace r C x) i)*Pilot.a template (dist i p/r)) =
      ∑ i,z i*(profile r C i-profile r (replace r C x) i)*Pilot.a template (dist i p/r) := by
      rw [←sum_sub_distrib]
      apply sum_congr rfl
      intro i _
      ring
    unfold integrand
    dsimp only [R]
    linear_combination 256*heq
  rw [hid]
  linarith

/-- The genuine heavy edit decrease, from compact minimizer local structure;
no pilot decrease is posed as a hypothesis. -/
theorem pilot_edit_drop {r γ δ : ℝ} (hr : 0<r) (C : Finset Y) (x : Y)
    {μ : Y → ℝ} (hμ : ∀ y,0≤μ y) (hγ0 : 0≤γ) (hγ : γ≤1/64)
    (hδ : δ≤1/4112) (hM : 0<Pilot.mass μ (Pilot.ball x (γ*r)))
    (hheavy : Pilot.mass μ (Pilot.ball x (51200*r)) ≤
      (1+δ)*Pilot.mass μ (Pilot.ball x (γ*r)))
    (hfar : ∀ a∈C,8*r<dist a x) :
    127*r*Pilot.mass μ (annulus x r) ≤
      potential template r μ (profile r C)-potential template r μ (profile r (replace r C x)) := by
  let z := minimizer template r μ (profile r C)
  have hz := (minimizer_spec template r μ (profile r C)).1
  have hmin := (minimizer_spec template r μ (profile r C)).2
  have hbsub : Pilot.ball x (γ*r) ⊆ Pilot.ball x (51200*r) := by
    intro y hy
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    have hd := (mem_filter.mp hy).2
    nlinarith
  have hconc : Pilot.mass μ (Pilot.ball x (100*template.R*r) \ Pilot.ball x (γ*r)) ≤
      δ*Pilot.mass μ (Pilot.ball x (γ*r)) := by
    have he := sum_sdiff (f := μ) hbsub
    change Pilot.mass μ (Pilot.ball x (51200*r) \ Pilot.ball x (γ*r))+
      Pilot.mass μ (Pilot.ball x (γ*r))=Pilot.mass μ (Pilot.ball x (51200*r)) at he
    norm_num [template] at *
    linarith
  have hlocal := local_structure (T := template) hr hγ0 hγ (by dsimp [template]; linarith)
    hδ hμ (profile_bounds r C)
    (by intro i j; simpa only [template,one_mul] using profile_lipschitz hr C i j)
    hz hmin hM hconc
  have hmiddle : ∀ i,r/4 ≤ dist i x → dist i x ≤ 256*r → z i=0 := by
    simpa only [z,template,one_mul,show (512:ℝ)*r/2=256*r by ring] using hlocal.1
  obtain ⟨a,ha,haz,_⟩ := hlocal.2
  have hnear : ∃ a,dist a x<r/4 ∧ (1/2:ℝ) ≤ z a :=
    ⟨a,by simpa only [template,one_mul] using ha,by linarith⟩
  have hpoint := sum_le_sum (s := (univ : Finset Y)) fun p _ =>
    mul_le_mul_of_nonneg_left (edit_integrand_drop hr C x hz hfar hmiddle hnear p) (hμ p)
  have hobj : 127*r*Pilot.mass μ (annulus x r) ≤
      objective template r μ (profile r C) z-
        objective template r μ (profile r (replace r C x)) z := by
    have he : (∑ p,μ p*(127*(if p∈annulus x r then (1:ℝ) else 0))) =
        127*Pilot.mass μ (annulus x r) := by
      simp only [mul_ite,mul_one,mul_zero,←sum_filter]
      simp only [filter_mem_eq_inter,Finset.univ_inter]
      rw [←sum_mul]
      simp only [Pilot.mass]
      ring
    rw [he] at hpoint
    have hm := mul_le_mul_of_nonneg_left hpoint hr.le
    simp only [mul_sub,sum_sub_distrib] at hm
    unfold objective
    convert hm using 1; (first | rfl | ring)
  have hnew := potential_le (μ := μ) (g := profile r (replace r C x)) hz
  change 127*r*Pilot.mass μ (annulus x r) ≤
    objective template r μ (profile r C) z-potential template r μ (profile r (replace r C x))
  linarith

end KServer.HeavyCenters

end


/-! The actual true-prefix heavy-center recursion of §07. All physical and
filtering steps are included in its potential budget, not only edit steps. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.HeavyCenters
open Pilot FiniteExperiment RankTracking PosteriorRanks
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]
variable {k H : ℕ} [NeZero k]

def Active (r γ δ : ℝ) (C : Finset Y) (μ : Y → ℝ) (x : Y) : Prop :=
  Pilot.mass μ (Pilot.ball x (51200*r)) ≤ (1+δ)*Pilot.mass μ (Pilot.ball x (γ*r)) ∧
    ∀ a∈C,8*r<dist a x

def step (r γ δ : ℝ) (C : Finset Y) (μ : Y → ℝ) (x : Y) : Finset Y :=
  if Active r γ δ C μ x then replace r C x else C

lemma step_separated (r γ δ : ℝ) (C : Finset Y) (μ : Y → ℝ) (x : Y)
    (hC : (C : Set Y).Pairwise (fun a b => 100*r<dist a b)) :
    ((step r γ δ C μ x : Finset Y) : Set Y).Pairwise (fun a b => 100*r<dist a b) := by
  unfold step
  split_ifs
  · intro a ha b hb hab
    rcases mem_insert.mp ha with rfl | ha
    · rcases mem_insert.mp hb with rfl | hb
      · exact (hab rfl).elim
      · have hd := (mem_filter.mp hb).2
        simpa only [dist_comm] using hd
    · rcases mem_insert.mp hb with rfl | hb
      · exact (mem_filter.mp ha).2
      · exact hC (mem_filter.mp ha).1 (mem_filter.mp hb).1 hab
  · exact hC

/-- Initially empty. End-of-input states are frozen; requests before then
use the genuine posterior at the new true prefix. -/
def centers (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (σ : Fin H → Y) : ℕ → Finset Y
  | 0 => ∅
  | t+1 => if ht : t<H then
      step r γ δ (centers s law r γ δ σ t) (mu s law (t+1) σ) (σ ⟨t,ht⟩)
    else centers s law r γ δ σ t

lemma centers_zero (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (σ : Fin H → Y) : centers s law r γ δ σ 0=∅ := rfl
lemma centers_succ (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (σ : Fin H → Y) (t : Fin H) :
    centers s law r γ δ σ (t.val+1)=
      step r γ δ (centers s law r γ δ σ t.val) (mu s law (t.val+1) σ) (σ t) := by
  simp only [centers,t.isLt,↓reduceDIte]

lemma centers_separated (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (σ : Fin H → Y) (t : ℕ) :
    ((centers s law r γ δ σ t : Finset Y) : Set Y).Pairwise (fun a b => 100*r<dist a b) := by
  induction t with
  | zero => simp [centers]
  | succ t ih =>
    rw [centers]
    split_ifs
    · exact step_separated r γ δ _ _ _ ih
    · exact ih

lemma centers_adapted (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (t : ℕ) :
    ∀ σ ρ,requestHistory t σ=requestHistory t ρ →
      centers s law r γ δ σ t=centers s law r γ δ ρ t := by
  induction t with
  | zero => intros; rfl
  | succ t ih =>
    intro σ ρ h
    have hc := ih σ ρ (requestHistory_refines t σ ρ h)
    have hμ : mu s law (t+1) σ=mu s law (t+1) ρ :=
      funext (fun y => mu_adapted s law (t+1) y σ ρ h)
    simp only [centers]
    split_ifs with ht
    · rw [hc,hμ,request_of_history ⟨t,ht⟩ σ ρ h]
    · exact hc

lemma inner_mass_pos (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (t : Fin H) (σ : Fin H → Y) (hσ : 0<law.val σ) {r γ : ℝ}
    (hr : 0<r) (hγ : 0≤γ) :
    0<Pilot.mass (mu s law (t.val+1) σ) (Pilot.ball (σ t) (γ*r)) := by
  have hx : σ t∈Pilot.ball (σ t) (γ*r) := by
    simp only [Pilot.ball,mem_filter,Finset.mem_univ,true_and,dist_self]
    exact mul_nonneg hγ hr.le
  have hm := single_le_sum (f := mu s law (t.val+1) σ)
    (fun y _ => mu_nonneg s law (t.val+1) σ y) hx
  exact lt_of_lt_of_le (by linarith [mu_served s law t σ hσ]) hm

/-- Exact annular charge made by a real center edit, zero on non-edit steps. -/
def charge (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (r γ δ : ℝ) (t : Fin H) (σ : Fin H → Y) : ℝ :=
  if Active r γ δ (centers s law r γ δ σ t.val) (mu s law (t.val+1) σ) (σ t)
  then r*Pilot.mass (mu s law (t.val+1) σ) (annulus (σ t) r) else 0

lemma charge_nonneg (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {r γ δ : ℝ} (hr : 0≤r) (t : Fin H) (σ : Fin H → Y) :
    0≤charge s law r γ δ t σ := by
  unfold charge
  split_ifs
  · exact mul_nonneg hr (Pilot.mass_nonneg (mu_nonneg s law (t.val+1) σ) _)
  · exact le_rfl

lemma charge_le_drop (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {r γ δ : ℝ} (hr : 0<r) (hγ0 : 0≤γ) (hγ : γ≤1/64) (hδ : δ≤1/4112)
    (t : Fin H) (σ : Fin H → Y) (hσ : 0<law.val σ) :
    charge s law r γ δ t σ ≤
      potential template r (mu s law (t.val+1) σ) (profile r (centers s law r γ δ σ t.val))-
      potential template r (mu s law (t.val+1) σ) (profile r (centers s law r γ δ σ (t.val+1))) := by
  rw [centers_succ]
  unfold charge step
  split_ifs with ha
  · have hd := pilot_edit_drop hr (centers s law r γ δ σ t.val) (σ t)
      (mu_nonneg s law (t.val+1) σ) hγ0 hγ hδ (inner_mass_pos s law t σ hσ hr hγ0) ha.1 ha.2
    have hn := mul_nonneg hr.le (Pilot.mass_nonneg (mu_nonneg s law (t.val+1) σ) (annulus (σ t) r))
    nlinarith
  · simp

/-- The source's all-step heavy-annulus budget for the actual adaptive
construction, with a finite endpoint bound independent of law and horizon. -/
theorem annulus_budget (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {γ δ r₀ τ : ℝ} (n p : ℕ)
    (hr : 0<r₀) (hτ : 2≤τ) (hγ0 : 0<γ) (hγ : γ≤1/64)
    (hδ0 : 0<δ) (hδ : δ≤1/4112) (hpow : 51200≤γ*(2:ℝ)^p) :
    (∑ t : Fin H,avg law.val (fun σ => ∑ j∈range n,
      charge s law (radius r₀ τ j) γ δ t σ)) ≤
      driftConstant template γ δ p*(1+Real.log ((k:ℝ)+1))*
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ)+
          ∑ j∈range n,2*radius r₀ τ j*(k:ℝ) := by
  let g := fun t σ j => profile (radius r₀ τ j) (centers s law (radius r₀ τ j) γ δ σ t)
  have hrad j : 0<radius r₀ τ j := radius_pos hr (by linarith) j
  have hb := pilot_edit_budget s law template (g := g) n p hr hτ hγ0
    (by dsimp [template]; exact le_min hγ (by linarith)) hδ0 hδ
    (by norm_num [template]; exact hpow)
    (by intro t σ j _ y; exact profile_bounds _ _ y)
    (by intro t σ j _ y z; simpa only [template,one_mul] using
      profile_lipschitz (hrad j) (centers s law (radius r₀ τ j) γ δ σ t) y z)
    (by intro t j _ y σ ρ hh; dsimp [g]; rw [centers_adapted s law _ γ δ t σ ρ hh])
  apply le_trans _ hb
  apply sum_le_sum
  intro t _
  apply sum_le_sum
  intro σ _
  by_cases hσ : 0<law.val σ
  · apply mul_le_mul_of_nonneg_left _ (law.property.1 σ)
    exact sum_le_sum fun j _ => charge_le_drop s law (hrad j) hγ0.le hγ hδ t σ hσ
  · have hz : law.val σ=0 := le_antisymm (le_of_not_gt hσ) (law.property.1 σ)
    simp [hz]

end KServer.HeavyCenters

end


/-! Fixed labels with a cooldown are constructed by finite online coloring.
A conflict set is a deterministic collection of previously reserved records;
labels are never used as random-tape indices. This is the finite pool mechanism
of §07, not a growing historical alphabet. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.OnlineLabels

variable {M : ℕ}

lemma unused_exists (s : Finset ℕ) (f : ℕ → Fin M) (hs : s.card<M) :
    ∃ c : Fin M, ∀ j ∈ s, f j≠c := by
  classical
  have hi : (s.image f).card < (univ : Finset (Fin M)).card := by
    simpa using (card_image_le.trans_lt hs)
  obtain ⟨c,_,hc⟩ := exists_mem_notMem_of_card_lt_card hi
  refine ⟨c,?_⟩
  intro j hj h
  exact hc (mem_image.mpr ⟨j,hj,h⟩)

/-- A finite coloring chosen at each insertion using only earlier colors. -/
def stage (hM : 0<M) (conflict : ℕ → Finset ℕ)
    (hcard : ∀ t, (conflict t).card<M) : ℕ → ℕ → Fin M
  | 0 => fun _ => ⟨0,hM⟩
  | t+1 => fun j => if j=t then
      (unused_exists (conflict t) (stage hM conflict hcard t) (hcard t)).choose
      else stage hM conflict hcard t j

lemma stage_step_old (hM : 0<M) (conflict : ℕ → Finset ℕ)
    (hcard : ∀ t, (conflict t).card<M) {i t : ℕ} (hi : i≠t) :
    stage hM conflict hcard (t+1) i=stage hM conflict hcard t i := by
  simp [stage,hi]

lemma stage_stable (hM : 0<M) (conflict : ℕ → Finset ℕ)
    (hcard : ∀ t, (conflict t).card<M) {i t : ℕ} (hi : i<t) :
    stage hM conflict hcard t i=stage hM conflict hcard (i+1) i := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases hit : i=t
      · subst i; rfl
      · rw [stage_step_old hM conflict hcard hit,ih (by omega)]

/-- Permanent color of a chronological record; later stages never modify it. -/
def color (hM : 0<M) (conflict : ℕ → Finset ℕ)
    (hcard : ∀ t, (conflict t).card<M) (i : ℕ) : Fin M :=
  stage hM conflict hcard (i+1) i

lemma color_avoids (hM : 0<M) (conflict : ℕ → Finset ℕ)
    (hcard : ∀ t, (conflict t).card<M)
    (hbefore : ∀ t, ∀ j ∈ conflict t, j<t) (t : ℕ) {j : ℕ}
    (hj : j ∈ conflict t) : color hM conflict hcard t≠color hM conflict hcard j := by
  have hi := (unused_exists (conflict t) (stage hM conflict hcard t) (hcard t)).choose_spec j hj
  rw [stage_stable hM conflict hcard (hbefore t j hj)] at hi
  simpa [color,stage] using Ne.symm hi

/-- If each simultaneous or cooldown pair was included when the later record
was inserted, the fixed pool colors it injectively. This local premise is on
record geometry, not an assumed random algorithm or cost estimate. -/
theorem color_injective_on (hM : 0<M) (conflict : ℕ → Finset ℕ)
    (hcard : ∀ t, (conflict t).card<M)
    (hbefore : ∀ t, ∀ j ∈ conflict t, j<t) (S : Set ℕ)
    (hpairs : ∀ i ∈ S, ∀ j ∈ S, j < i → j ∈ conflict i) :
    Set.InjOn (color hM conflict hcard) S := by
  intro i hi j hj he
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (color_avoids hM conflict hcard hbefore j (hpairs j hj i hi hij) he.symm)
  · exact hij
  · exact False.elim (color_avoids hM conflict hcard hbefore i (hpairs i hi j hj hij) he)

/-- The source's 4M+4 pool has strictly more slots than the two reserved sets
and two new records excluded by a one-step cooldown. -/
lemma cooldown_card (A B fresh : Finset ℕ) {N : ℕ}
    (hA : A.card ≤ N) (hB : B.card ≤ N) (hf : fresh.card ≤ 2) :
    (A∪B∪fresh).card < 4*N+4 := by
  have h := card_union_le (A∪B) fresh
  have h' := card_union_le A B
  omega

end KServer.OnlineLabels

end


/-! Actual finite heavy-ball label update. Intersections in the finite metric
force reuse; otherwise the new label avoids both current and previous labels.
No region, anchor or label lifetime is assumed. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavyLabels
open HeavyCenters
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y]

abbrev Pool (Y : Type*) [Fintype Y] := Fin (4*Fintype.card Y+4)
def overlap (C : Finset Y) (rad : Y → ℝ) (x : Y) (R : ℝ) : Finset Y :=
  C.filter (fun a => ∃ p : Y, dist a p≤rad a ∧ dist x p≤R)

lemma overlap_distance {C : Finset Y} {rad : Y → ℝ} {x a : Y} {r R : ℝ}
    (hrad : ∀ a∈C,rad a≤20*r) (hR : R≤20*r) (ha : a∈overlap C rad x R) :
    dist a x≤40*r := by
  obtain ⟨ha,p,hp,hx⟩ := mem_filter.mp ha
  have ht:=dist_triangle a p x
  rw [dist_comm p x] at ht
  linarith [hrad a ha]

lemma overlap_unique {C : Finset Y} {rad : Y → ℝ} {x a b : Y} {r R : ℝ}
    (hr : 0<r) (hC : (C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad : ∀ a∈C,rad a≤20*r) (hR : R≤20*r)
    (ha : a∈overlap C rad x R) (hb : b∈overlap C rad x R) : a=b := by
  by_contra hn
  have hd:=hC (mem_filter.mp ha).1 (mem_filter.mp hb).1 hn
  have h1:=overlap_distance hrad hR ha
  have h2:=overlap_distance hrad hR hb
  have ht:=dist_triangle a x b
  rw [dist_comm x b] at ht
  linarith

omit [MetricSpace Y] in
lemma unused (C D : Finset Y) (label prev : Y → Pool Y) :
    ∃ i : Pool Y, i∉C.image label ∧ i∉D.image prev := by
  have hC : (C.image label).card≤Fintype.card Y := card_image_le.trans C.card_le_univ
  have hD : (D.image prev).card≤Fintype.card Y := card_image_le.trans D.card_le_univ
  have hh : (C.image label∪D.image prev).card<(univ:Finset (Pool Y)).card := by
    have hu:=card_union_le (C.image label) (D.image prev)
    simp only [card_univ,Fintype.card_fin]
    omega
  obtain ⟨i,_,hi⟩:=exists_mem_notMem_of_card_lt_card hh
  exact ⟨i,fun h=>hi (mem_union_left _ h),fun h=>hi (mem_union_right _ h)⟩

def fresh (C D : Finset Y) (label prev : Y → Pool Y) : Pool Y := (unused C D label prev).choose
omit [MetricSpace Y] in
lemma fresh_avoids (C D : Finset Y) (label prev : Y → Pool Y) :
    fresh C D label prev∉C.image label ∧ fresh C D label prev∉D.image prev :=
  (unused C D label prev).choose_spec

def insertedLabel (C D : Finset Y) (rad : Y → ℝ) (label prev : Y → Pool Y) (x : Y) (R : ℝ) : Pool Y :=
  if h:(overlap C rad x R).Nonempty then label h.choose else fresh C D label prev

def updatedLabel (C D : Finset Y) (rad : Y → ℝ) (label prev : Y → Pool Y) (x : Y) (R : ℝ) : Y → Pool Y :=
  Function.update label x (insertedLabel C D rad label prev x R)

lemma inserted_reuses {C D : Finset Y} {rad : Y → ℝ} {label prev : Y → Pool Y} {x a : Y} {r R : ℝ}
    (hr : 0<r) (hC : (C:Set Y).Pairwise (fun a b=>100*r<dist a b))
    (hrad : ∀ a∈C,rad a≤20*r) (hR : R≤20*r) (ha : a∈overlap C rad x R) :
    insertedLabel C D rad label prev x R=label a := by
  have h : (overlap C rad x R).Nonempty:=⟨a,ha⟩
  rw [insertedLabel,dite_eq_left h]
  rw [overlap_unique hr hC hrad hR h.choose_spec ha]

lemma existing_match {C D : Finset Y} {rad : Y → ℝ} {label prev : Y → Pool Y} {x a : Y} {R : ℝ}
    (hl : Set.InjOn label (C:Set Y)) (ha : a∈C)
    (he : insertedLabel C D rad label prev x R=label a) : a∈overlap C rad x R := by
  unfold insertedLabel at he
  split_ifs at he with h
  · have heq:=hl (mem_filter.mp h.choose_spec).1 ha he
    exact heq ▸ h.choose_spec
  · exact False.elim ((fresh_avoids C D label prev).1 (mem_image.mpr ⟨a,ha,he.symm⟩))

lemma inserted_diff_kept {C D : Finset Y} {rad : Y → ℝ} {label prev : Y → Pool Y} {x a : Y} {r R : ℝ}
    (hr : 0<r) (hrad : ∀ a∈C,rad a≤20*r) (hR : R≤20*r)
    (hl : Set.InjOn label (C:Set Y)) (ha : a∈C) (hd : 100*r<dist a x) :
    insertedLabel C D rad label prev x R≠label a := by
  intro he
  have hh:=overlap_distance hrad hR (existing_match hl ha he)
  linarith

/-- An actual update preserves injective active heavy labels. -/
lemma update_injective {C D : Finset Y} {rad : Y → ℝ} {label prev : Y → Pool Y} {x : Y} {r R : ℝ}
    (hr : 0<r) (hrad : ∀ a∈C,rad a≤20*r) (hR : R≤20*r)
    (hl : Set.InjOn label (C:Set Y)) :
    Set.InjOn (updatedLabel C D rad label prev x R) (replace r C x:Set Y) := by
  intro a ha b hb he
  rcases mem_insert.mp ha with hax|ha
  · subst a
    rcases mem_insert.mp hb with hbx|hb
    · exact hbx.symm
    · have hbx : b≠x := by
        intro hh; have hd:=(mem_filter.mp hb).2; simp only [hh,dist_self] at hd; linarith
      simp only [updatedLabel,Function.update_self,Function.update_of_ne hbx] at he
      exact False.elim (inserted_diff_kept hr hrad hR hl (mem_filter.mp hb).1 (mem_filter.mp hb).2 he)
  · rcases mem_insert.mp hb with hbx|hb
    · subst b
      have hax : a≠x := by
        intro hh; have hd:=(mem_filter.mp ha).2; simp only [hh,dist_self] at hd; linarith
      simp only [updatedLabel,Function.update_self,Function.update_of_ne hax] at he
      exact False.elim (inserted_diff_kept hr hrad hR hl (mem_filter.mp ha).1 (mem_filter.mp ha).2 he.symm)
    · have hax : a≠x := by
        intro hh; have hd:=(mem_filter.mp ha).2; simp only [hh,dist_self] at hd; linarith
      have hbx : b≠x := by
        intro hh; have hd:=(mem_filter.mp hb).2; simp only [hh,dist_self] at hd; linarith
      simp only [updatedLabel,Function.update_of_ne hax,Function.update_of_ne hbx] at he
      exact hl (mem_filter.mp ha).1 (mem_filter.mp hb).1 he

/-- Every common coordinate label keeps its anchor, except for a genuine
intersecting-ball reuse; in that case it moves at most40r. -/
lemma common_anchor {C D : Finset Y} {rad : Y → ℝ} {label prev : Y → Pool Y} {x a b : Y} {r R : ℝ}
    (hrad : ∀ a∈C,rad a≤20*r) (hR : R≤20*r)
    (hl : Set.InjOn label (C:Set Y)) (ha : a∈C) (hb : b∈replace r C x)
    (he : label a=updatedLabel C D rad label prev x R b) : a=b ∨ dist a b≤40*r := by
  by_cases hbx : b=x
  · subst b
    simp only [updatedLabel,Function.update_self] at he
    exact Or.inr (overlap_distance hrad hR (existing_match hl ha he.symm))
  · have hbC : b∈C := (mem_filter.mp ((mem_insert.mp hb).resolve_left hbx)).1
    simp only [updatedLabel,Function.update_of_ne hbx] at he
    exact Or.inl (hl ha hbC he)
end KServer.HeavyLabels

end


/-! Exact truncated exponential tails and first-hit cancellation used by the
chronological finite-law partition construction, manuscript §07.  The radius
law is not replaced by a uniform/padded law: `tail` is its exact tail. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PartitionProbabilities

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Normalized clipped position in the source radius interval `[r,2*r]`. -/
def position (r a : ℝ) : ℝ := min (max (a/r-1) 0) 1

lemma position_range (r a : ℝ) : position r a ∈ Set.Icc (0:ℝ) 1 := by
  dsimp [position]
  exact ⟨le_min (le_max_right _ _) (by norm_num), min_le_right _ _⟩

lemma position_mono {r : ℝ} (hr : 0 < r) : Monotone (position r) := by
  intro a b hab
  exact min_le_min_right _ (max_le_max_right _ (sub_le_sub_right (div_le_div_of_nonneg_right hab hr.le) _))

lemma position_difference {r a b : ℝ} (hr : 0 < r) (hab : a ≤ b) :
    position r b-position r a ≤ (b-a)/r := by
  have hdiv : a/r ≤ b/r := div_le_div_of_nonneg_right hab hr.le
  have hd : (b-a)/r = b/r-a/r := sub_div _ _ _
  rw [hd]
  unfold position
  rcases le_total (a/r-1) 0 with ha | ha
  · rw [max_eq_right ha, min_eq_left (by norm_num : (0:ℝ) ≤ 1)]
    rcases le_total (b/r-1) 0 with hb | hb
    · rw [max_eq_right hb, min_eq_left (by norm_num : (0:ℝ) ≤ 1)]
      linarith
    · rw [max_eq_left hb]
      linarith [min_le_left (b/r-1) (1:ℝ)]
  · rw [max_eq_left ha, max_eq_left (ha.trans (sub_le_sub_right hdiv _))]
    rcases le_total (a/r-1) 1 with ha' | ha'
    · rw [min_eq_left ha']
      linarith [min_le_left (b/r-1) 1]
    · rw [min_eq_right ha', min_eq_right (ha'.trans (sub_le_sub_right hdiv _))]
      linarith

/-- The exact tail of the density in eq. tier-radius-density.  The clipped
formula includes both support endpoints (which have zero atom). -/
def tail (lam r a : ℝ) : ℝ :=
  (Real.exp (lam*(1-position r a))-1)/(Real.exp lam-1)

lemma tail_range {lam : ℝ} (hlam : 0 < lam) (r a : ℝ) :
    tail lam r a ∈ Set.Icc (0:ℝ) 1 := by
  have he : 0 < Real.exp lam-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hlam)
  have hu := position_range r a
  have hlow : 1 ≤ Real.exp (lam*(1-position r a)) := Real.one_le_exp (by nlinarith [hu.2])
  have hup : Real.exp (lam*(1-position r a)) ≤ Real.exp lam :=
    Real.exp_le_exp.mpr (by nlinarith [hu.1])
  exact ⟨div_nonneg (by linarith) he.le, (div_le_one he).mpr (by linarith)⟩

lemma tail_antitone {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) : Antitone (tail lam r) := by
  intro a b hab
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr (Real.one_le_exp hlam.le))
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (position_mono hr hab) _) hlam.le

lemma position_of_le {r a : ℝ} (hr : 0 < r) (ha : a ≤ r) : position r a=0 := by
  have h : a/r-1 ≤ 0 := by have := (div_le_one hr).mpr ha; linarith
  simp [position,max_eq_right h]

lemma position_of_ge {r a : ℝ} (hr : 0 < r) (ha : 2*r ≤ a) : position r a=1 := by
  have h : 1 ≤ a/r-1 := by have := (le_div_iff₀ hr).mpr ha; linarith
  rw [position, max_eq_left (by linarith), min_eq_right h]

lemma tail_of_le {lam r a : ℝ} (hlam : 0 < lam) (hr : 0 < r) (ha : a ≤ r) :
    tail lam r a=1 := by
  simp [tail,position_of_le hr ha,ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hlam))]

lemma tail_of_ge {lam r a : ℝ} (hr : 0 < r) (ha : 2*r ≤ a) : tail lam r a=0 := by
  simp [tail,position_of_ge hr ha]

/-- Elementary exponential secant bound, including arbitrary negative inputs. -/
lemma exp_difference_le (u v : ℝ) : Real.exp u-Real.exp v ≤ (u-v)*Real.exp u := by
  have h := Real.add_one_le_exp (v-u)
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_nonneg u)
  rw [← Real.exp_add] at hm
  have he : v-u+u=v := by ring
  rw [he] at hm
  nlinarith

/-- The source first-hit tail inequality, valid even if the interval crosses
one or both endpoints of the radius support. -/
theorem tail_interval_bound {lam r a b : ℝ} (hlam : 0 < lam) (hr : 0 < r) (hab : a ≤ b) :
    tail lam r a-tail lam r b ≤
      (lam*(b-a)/r)*(tail lam r a+1/(Real.exp lam-1)) := by
  let c := Real.exp lam-1
  have hc : 0 < c := sub_pos.mpr (Real.one_lt_exp_iff.mpr hlam)
  have hd := position_difference hr hab
  have hE := exp_difference_le (lam*(1-position r a)) (lam*(1-position r b))
  have hE' : Real.exp (lam*(1-position r a))-Real.exp (lam*(1-position r b)) ≤
      (lam*(b-a)/r)*Real.exp (lam*(1-position r a)) := by
    refine hE.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    calc lam*(1-position r a)-lam*(1-position r b) = lam*(position r b-position r a) := by ring
         _ ≤ lam*((b-a)/r) := mul_le_mul_of_nonneg_left hd hlam.le
         _ = lam*(b-a)/r := by ring
  have hdiv := div_le_div_of_nonneg_right hE' hc.le
  dsimp [tail]
  dsimp [c] at hdiv hc
  convert hdiv using 1 <;> first | rfl | ring

/-- Prefix miss probabilities for independent records in chronological order. -/
def prefixMiss (p : ℕ → ℝ) (n : ℕ) : ℝ := ∏ i ∈ range n, (1-p i)

lemma prefixMiss_zero (p : ℕ → ℝ) : prefixMiss p 0=1 := by simp [prefixMiss]
lemma prefixMiss_succ (p : ℕ → ℝ) (n : ℕ) :
    prefixMiss p (n+1)=prefixMiss p n*(1-p n) := by simp [prefixMiss,prod_range_succ]

lemma prefixMiss_range {p : ℕ → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    prefixMiss p n ∈ Set.Icc (0:ℝ) 1 := by
  induction n with
  | zero => simp [prefixMiss]
  | succ n ih =>
      rw [prefixMiss_succ]
      exact ⟨mul_nonneg ih.1 (by linarith [(hp n).2]),
        (mul_le_mul_of_nonneg_left (by linarith [(hp n).1] : 1-p n ≤ 1) ih.1).trans (by simpa using ih.2)⟩

/-- Exact first-hit partition of the probability of at least one hit. -/
theorem first_hit_sum (p : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, prefixMiss p i*p i)=1-prefixMiss p n := by
  induction n with
  | zero => simp [prefixMiss]
  | succ n ih => rw [sum_range_succ,ih,prefixMiss_succ]; ring

/-- First-hit separation bound after conditioning on presences. It sums the
individual tail coefficients, rather than paying for all K² hits separately. -/
theorem first_hit_bound {p s : ℕ → ℝ} {c ε : ℝ} (n : ℕ)
    (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hs : ∀ i < n, s i ≤ c*(p i+ε)) :
    (∑ i ∈ range n, prefixMiss p i*s i) ≤ c*(1+ε*n) := by
  have hsum : (∑ i ∈ range n, prefixMiss p i*s i) ≤
      c*((∑ i ∈ range n, prefixMiss p i*p i)+ε*∑ i ∈ range n, prefixMiss p i) := by
    calc (∑ i ∈ range n, prefixMiss p i*s i) ≤ ∑ i ∈ range n, prefixMiss p i*(c*(p i+ε)) := by
           apply sum_le_sum
           intro i hi
           exact mul_le_mul_of_nonneg_left (hs i (mem_range.mp hi)) (prefixMiss_range hp i).1
         _ = _ := by
           simp_rw [show ∀ i, prefixMiss p i*(c*(p i+ε)) = c*(prefixMiss p i*p i)+c*ε*prefixMiss p i by intro i; ring]
           rw [sum_add_distrib, ← mul_sum, ← mul_sum]
           ring
  refine hsum.trans (mul_le_mul_of_nonneg_left ?_ hc)
  rw [first_hit_sum]
  have hpref : (∑ i ∈ range n, prefixMiss p i) ≤ n := by
    calc (∑ i ∈ range n, prefixMiss p i) ≤ ∑ _i ∈ range n, (1:ℝ) := sum_le_sum fun i _ => (prefixMiss_range hp i).2
         _ = n := by simp
  have := mul_le_mul_of_nonneg_left hpref hε
  have := (prefixMiss_range hp n).1
  linarith

section FiniteProduct
variable {I : Type*} [Fintype I] {Ω : I → Type*} [∀ i, Fintype (Ω i)]

/-- Literal independent product tape; independence is proved by multiplication,
not postulated as an assumption about adaptive states. -/
def productWeight (w : ∀ i, Ω i → ℝ) (o : ∀ i, Ω i) : ℝ := ∏ i, w i (o i)

def probability (w : ∀ i, Ω i → ℝ) (event : (∀ i, Ω i) → Prop) : ℝ := by
  classical
  exact ∑ o, if event o then productWeight w o else 0

omit [∀ i, Fintype (Ω i)] in
lemma productWeight_nonneg {w : ∀ i, Ω i → ℝ} (hw : ∀ i a, 0 ≤ w i a)
    (o : ∀ i, Ω i) : 0 ≤ productWeight w o := prod_nonneg fun i _ => hw i (o i)

lemma productWeight_sum (w : ∀ i, Ω i → ℝ) (hw : ∀ i, ∑ a, w i a=1) :
    ∑ o, productWeight w o=1 := by
  classical
  simp only [productWeight, ← Fintype.prod_sum]
  simp [hw]

lemma product_expectation (w f : ∀ i, Ω i → ℝ) :
    (∑ o, productWeight w o*∏ i, f i (o i))=∏ i, ∑ a, w i a*f i a := by
  classical
  simp only [productWeight, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => w i a*f i a)).symm

lemma rectangle_probability (w : ∀ i, Ω i → ℝ) (E : ∀ i, Ω i → Prop) :
    probability w (fun o => ∀ i, E i (o i))=∏ i, ∑ a, if E i a then w i a else 0 := by
  classical
  rw [probability, Fintype.prod_sum]
  apply sum_congr rfl
  intro o _
  by_cases h : ∀ i, E i (o i)
  · simp [h, productWeight]
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    symm
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

lemma probability_range {w : ∀ i, Ω i → ℝ} (hw : ∀ i a, 0 ≤ w i a)
    (hsum : ∀ i, ∑ a, w i a=1) (E : (∀ i, Ω i) → Prop) :
    probability w E ∈ Set.Icc (0:ℝ) 1 := by
  classical
  refine ⟨sum_nonneg (fun o _ => ?_), ?_⟩
  · split_ifs
    · exact productWeight_nonneg hw o
    · rfl
  · calc probability w E ≤ ∑ o, productWeight w o := by
           apply sum_le_sum
           intro o _
           split_ifs
           · rfl
           · exact productWeight_nonneg hw o
         _ = 1 := productWeight_sum w hsum

omit [Fintype I] in
lemma complement_probability (w : ∀ i, Ω i → ℝ) (i : I) (E : Ω i → Prop)
    (hw : ∑ a, w i a=1) :
    (∑ a, if ¬E a then w i a else 0)=1-∑ a, if E a then w i a else 0 := by
  classical
  have he : (∑ a, if ¬E a then w i a else 0)+(∑ a, if E a then w i a else 0)=1 := by
    rw [← sum_add_distrib, ← hw]
    apply sum_congr rfl
    intro a _
    split_ifs <;> simp_all
  linarith
end FiniteProduct

section FirstSeparation
variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)]

/-- Exactly the source separating-first-hit event in chronological order. -/
def firstSeparation (hit sep : ∀ i, Ω i → Prop) (o : ∀ i, Ω i) : Prop :=
  ∃ i, sep i (o i) ∧ ∀ j, j < i → ¬hit j (o j)

def firstAt (hit sep : ∀ i, Ω i → Prop) (i : Fin n) (o : ∀ i, Ω i) : Prop :=
  sep i (o i) ∧ ∀ j, j < i → ¬hit j (o j)

omit [∀ i, Fintype (Ω i)] in
lemma firstAt_unique {hit sep : ∀ i, Ω i → Prop} (hs : ∀ i a, sep i a → hit i a)
    {o : ∀ i, Ω i} {i j : Fin n} (hi : firstAt hit sep i o) (hj : firstAt hit sep j o) : i=j := by
  rcases lt_trichotomy i j with h | h | h
  · exact False.elim (hj.2 i h (hs i (o i) hi.1))
  · exact h
  · exact False.elim (hi.2 j h (hs j (o j) hj.1))

lemma firstSeparation_probability {hit sep : ∀ i, Ω i → Prop}
    (hs : ∀ i a, sep i a → hit i a) (w : ∀ i, Ω i → ℝ) :
    probability w (firstSeparation hit sep)=∑ i, probability w (firstAt hit sep i) := by
  classical
  unfold probability
  rw [sum_comm]
  apply sum_congr rfl
  intro o _
  by_cases h : firstSeparation hit sep o
  · rw [ite_eq_left h]
    obtain ⟨i,hi⟩ := h
    change firstAt hit sep i o at hi
    symm
    rw [sum_eq_single i, ite_eq_left hi]
    · intro j _ hji
      rw [ite_eq_right (fun hj => hji (firstAt_unique hs hj hi))]
    · exact fun hnot => False.elim (hnot (mem_univ i))
  · rw [ite_eq_right h]
    symm
    apply sum_eq_zero
    intro i _
    exact ite_eq_right (fun hi => h ⟨i,hi⟩)

/-- Evaluation of one first-hit rectangle under the constructed product tape. -/
lemma firstAt_probability {hit sep : ∀ i, Ω i → Prop}
    (w : ∀ i, Ω i → ℝ) (hw : ∀ i, ∑ a, w i a=1) (i : Fin n) :
    probability w (firstAt hit sep i)=
      (∑ a, if sep i a then w i a else 0) *
        ∏ j ∈ univ.filter (fun j : Fin n => j < i), (1 - ∑ a, if hit j a then w j a else 0) := by
  classical
  let E : ∀ j, Ω j → Prop := fun j a => (j=i → sep j a) ∧ (j < i → ¬hit j a)
  have he : firstAt hit sep i=(fun o => ∀ j, E j (o j)) := by
    funext o
    apply propext
    constructor
    · intro h j
      exact ⟨fun hj => by subst j; exact h.1, h.2 j⟩
    · intro h
      exact ⟨(h i).1 rfl, fun j hj => (h j).2 hj⟩
  rw [he,rectangle_probability]
  have hfac (j : Fin n) : (∑ a, @ite ℝ (E j a) (Classical.propDecidable _) (w j a) 0)=
      (if j=i then (∑ a, if sep j a then w j a else 0) else 1)*
      (if j < i then (1-∑ a, if hit j a then w j a else 0) else 1) := by
    by_cases hji : j=i
    · subst j
      simp [E]
    · by_cases hj : j < i
      · simp only [E,hji,hj,false_implies,true_implies,true_and,ite_false,ite_true,one_mul]
        exact complement_probability w j (hit j) (hw j)
      · simp [E,hji,hj,hw]
  calc
    (∏ j, ∑ a, @ite ℝ (E j a) (Classical.propDecidable _) (w j a) 0) = ∏ j, ((if j=i then (∑ a, if sep j a then w j a else 0) else 1)*
      (if j < i then (1-∑ a, if hit j a then w j a else 0) else 1)) :=
        prod_congr rfl (fun j _ => hfac j)
    _ = _ := by
      rw [prod_mul_distrib]
      simp only [prod_ite_eq',mem_univ,ite_true]
      congr 1
      rw [prod_filter]

/-- The chronological first-hit estimate under the literal finite product law.
No independence is asserted for an adaptive filtration: this theorem applies
only after its deterministic schedule and surviving indices have been fixed. -/
theorem independent_first_hit_bound {hit sep : ∀ i, Ω i → Prop}
    (w : ∀ i, Ω i → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hw1 : ∀ i, ∑ a, w i a=1) (hsep : ∀ i a, sep i a → hit i a)
    {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hm : ∀ i, (∑ a, if sep i a then w i a else 0) ≤
      c*((∑ a, if hit i a then w i a else 0)+ε)) :
    probability w (firstSeparation hit sep) ≤ c*(1+ε*n) := by
  classical
  let p : Fin n → ℝ := fun i => ∑ a, if hit i a then w i a else 0
  have hp (i : Fin n) : p i ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨sum_nonneg (fun a _ => ?_), ?_⟩
    · split_ifs
      · exact hw i a
      · rfl
    · calc p i ≤ ∑ a, w i a := by
             apply sum_le_sum
             intro a _
             split_ifs
             · rfl
             · exact hw i a
           _ = 1 := hw1 i
  let q : Fin n → ℝ := fun i => ∏ j ∈ univ.filter (fun j : Fin n => j < i), (1-p j)
  have hq (i : Fin n) : q i ∈ Set.Icc (0:ℝ) 1 := by
    exact ⟨prod_nonneg (fun j _ => sub_nonneg.mpr (hp j).2),
      prod_le_one₀ (fun index _ => sub_nonneg.mpr (hp index).2)
        (fun index _ => by linarith [(hp index).1])⟩
  have hb (i : Fin n) : probability w (firstAt hit sep i) ≤
      c*(probability w (firstAt hit hit i)+ε) := by
    rw [firstAt_probability w hw1,firstAt_probability w hw1]
    change (∑ a, if sep i a then w i a else 0)*q i ≤ c*(p i*q i+ε)
    calc _ ≤ (c*(p i+ε))*q i := mul_le_mul_of_nonneg_right (hm i) (hq i).1
         _ ≤ _ := by nlinarith only [mul_nonneg hc (mul_nonneg hε (by linarith [(hq i).2] : 0 ≤ 1-q i))]
  calc probability w (firstSeparation hit sep) = ∑ i, probability w (firstAt hit sep i) :=
         firstSeparation_probability hsep w
       _ ≤ ∑ i, c*(probability w (firstAt hit hit i)+ε) := sum_le_sum (fun i _ => hb i)
       _ = c*(probability w (firstSeparation hit hit)+ε*n) := by
         rw [← mul_sum,sum_add_distrib,← firstSeparation_probability (fun _ _ h => h) w]
         simp [mul_comm]
       _ ≤ c*(1+ε*n) := mul_le_mul_of_nonneg_left
         (add_le_add (probability_range hw hw1 _).2 le_rfl) hc

end FirstSeparation

end KServer.PartitionProbabilities

end


/-! Finite inverse-tail sampling for the chronological tape. It applies both
to retirement ages and to the finitely many observable radius thresholds. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteSurvival

/-- A finite lifetime `d` is alive at ages `0,...,d`. -/
def weight (s : ℕ → ℝ) {N : ℕ} (d : Fin N) : ℝ := s d-s (d+1)

def probability {N : ℕ} (s : ℕ → ℝ) (E : Fin N → Prop) : ℝ := by
  classical
  exact ∑ d, if E d then weight s d else 0

lemma weight_nonneg {s : ℕ → ℝ} (hs : Antitone s) {N : ℕ} (d : Fin N) :
    0 ≤ weight s d := sub_nonneg.mpr (hs (Nat.le_succ _))

lemma weight_sum (s : ℕ → ℝ) (N : ℕ) : ∑ d : Fin N, weight s d=s 0-s N := by
  unfold weight
  rw [Fin.sum_univ_eq_sum_range (fun i => s i-s (i+1)), sum_range_sub']

lemma probability_living (s : ℕ → ℝ) (N a : ℕ) (ha : a ≤ N) :
    probability s (fun d : Fin N => a ≤ (d:ℕ))=s a-s N := by
  classical
  have heq : probability s (fun d : Fin N => a ≤ (d:ℕ))=
      ∑ d : Fin N, if a ≤ (d:ℕ) then s d-s (d+1) else 0 := by
    apply sum_congr rfl
    intro d _
    by_cases h : a ≤ (d:ℕ) <;> simp [h,weight]
  rw [heq,Fin.sum_univ_eq_sum_range (fun d => if a ≤ d then s d-s (d+1) else 0)]
  have hf : (range N).filter (fun d => a ≤ d)=Ico a N := by
    ext d
    simp only [mem_filter,mem_range,mem_Ico]
    omega
  rw [← sum_filter,hf]
  have h := sum_Ico_sub s ha
  have he : (∑ d ∈ Ico a N, (s d-s (d+1))) =
      -(∑ d ∈ Ico a N, (s (d+1)-s d)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro d _
    ring
  rw [he,h]
  ring

/-- An actual finite probability law realizes every prescribed decreasing
survival tail exactly; this is the finite inverse-tail construction, not an
independence or randomness assumption. -/
theorem inverse_tail {s : ℕ → ℝ} {N : ℕ} (hs : Antitone s)
    (hs0 : s 0=1) (hsN : s N=0) :
    (∀ d : Fin N, 0 ≤ weight s d) ∧ (∑ d : Fin N, weight s d=1) ∧
      ∀ a ≤ N, probability s (fun d : Fin N => a ≤ (d:ℕ))=s a := by
  refine ⟨weight_nonneg hs,?_,?_⟩
  · rw [weight_sum,hs0,hsN,sub_zero]
  · intro a ha
    rw [probability_living _ _ _ ha,hsN,sub_zero]

/-- The exact probability of a single-bin threshold crossing. -/
lemma probability_crossing (s : ℕ → ℝ) (N a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    probability s (fun d : Fin N => a ≤ (d:ℕ) ∧ (d:ℕ)<b)=s a-s b := by
  classical
  have he : probability s (fun d : Fin N => a ≤ (d:ℕ) ∧ (d:ℕ)<b)=
      probability s (fun d : Fin N => a ≤ (d:ℕ))-
      probability s (fun d : Fin N => b ≤ (d:ℕ)) := by
    unfold probability
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro d _
    split_ifs <;> simp_all <;> omega
  rw [he,probability_living _ _ _ (hab.trans hb),probability_living _ _ _ hb]
  ring

end KServer.FiniteSurvival

end


/-! Finite discretization of the manuscript's truncated exponential radius.
All pairwise-distance decisions are included in a finite ordered grid; its
literal tail law yields a finite tape, without invoking assumed independence. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteRadius
open PartitionProbabilities FiniteSurvival
attribute [local instance] Classical.propDecidable Classical.decEq

def grid (D : Finset ℝ) (r : ℝ) : Finset ℝ := insert r (insert (2*r) (D.filter (fun a=>r≤a ∧ a≤2*r)))

lemma grid_pos (D : Finset ℝ) (r : ℝ) : 0<(grid D r).card :=
  card_pos.mpr ⟨r,mem_insert_self _ _⟩

def point (D : Finset ℝ) (r : ℝ) (i : Fin (grid D r).card) : ℝ :=
  ((grid D r).orderIsoOfFin rfl i).val

lemma point_mono (D : Finset ℝ) (r : ℝ) : StrictMono (point D r) :=
  ((grid D r).orderEmbOfFin rfl).strictMono

lemma point_range (D : Finset ℝ) {r : ℝ} (hr : 0<r) (i : Fin (grid D r).card) :
    point D r i∈Set.Icc r (2*r) := by
  have hi : point D r i∈grid D r := ((grid D r).orderIsoOfFin rfl i).property
  change point D r i∈insert r (insert (2*r) (D.filter (fun a=>r≤a ∧ a≤2*r))) at hi
  simp only [mem_insert,mem_filter] at hi
  rcases hi with he|he|⟨_,he⟩
  · rw [he]; exact ⟨le_rfl,by linarith⟩
  · rw [he]; exact ⟨by linarith,le_rfl⟩
  · exact he

lemma point_zero (D : Finset ℝ) {r : ℝ} (hr : 0<r) :
    point D r ⟨0,grid_pos D r⟩=r := by
  let i:=((grid D r).orderIsoOfFin rfl).symm ⟨r,mem_insert_self _ _⟩
  have he : point D r i=r := congrArg Subtype.val (((grid D r).orderIsoOfFin rfl).apply_symm_apply _)
  have hm:point D r ⟨0,grid_pos D r⟩≤point D r i := (point_mono D r).monotone (Nat.zero_le _)
  exact le_antisymm (hm.trans_eq he) (point_range D hr _).1

def survival (D : Finset ℝ) (lam r : ℝ) (a : ℕ) : ℝ :=
  if ha:a<(grid D r).card then tail lam r (point D r ⟨a,ha⟩) else 0

lemma survival_fin (D : Finset ℝ) (lam r : ℝ) (a : Fin (grid D r).card) :
    survival D lam r a=tail lam r (point D r a) := by simp [survival,a.isLt]

lemma survival_zero (D : Finset ℝ) {lam r : ℝ} (hlam : 0<lam) (hr : 0<r) :
    survival D lam r 0=1 := by
  rw [survival, dite_eq_left (grid_pos D r),point_zero D hr]
  exact tail_of_le hlam hr le_rfl

lemma survival_last (D : Finset ℝ) (lam r : ℝ) :
    survival D lam r (grid D r).card=0 := by simp [survival]

lemma survival_nonneg (D : Finset ℝ) {lam r : ℝ} (hlam : 0<lam) (a : ℕ) :
    0 ≤ survival D lam r a := by
  unfold survival; split_ifs
  · exact (tail_range hlam _ _).1
  · rfl

lemma survival_antitone (D : Finset ℝ) {lam r : ℝ} (hlam : 0<lam) (hr : 0<r) :
    Antitone (survival D lam r) := by
  intro a b hab
  by_cases hb:b<(grid D r).card
  · have ha:a<(grid D r).card := lt_of_le_of_lt hab hb
    rw [survival,dite_eq_left hb,survival,dite_eq_left ha]
    exact tail_antitone hlam hr ((point_mono D r).monotone hab)
  · rw [survival,dite_eq_right hb]
    exact survival_nonneg D hlam a

/-- Weights of the actual finite radius outcome. -/
def weights (D : Finset ℝ) (lam r : ℝ) (i : Fin (grid D r).card) : ℝ :=
  weight (survival D lam r) i

lemma weights_nonneg (D : Finset ℝ) {lam r : ℝ} (hlam : 0<lam) (hr : 0<r)
    (i : Fin (grid D r).card) : 0≤weights D lam r i :=
  weight_nonneg (survival_antitone D hlam hr) i

lemma weights_sum (D : Finset ℝ) {lam r : ℝ} (hlam : 0<lam) (hr : 0<r) :
    ∑ i,weights D lam r i=1 := by
  change (∑ i : Fin (grid D r).card,weight (survival D lam r) i)=1
  rw [weight_sum,survival_zero D hlam hr,survival_last]
  norm_num

lemma grid_tail (D : Finset ℝ) {lam r a : ℝ} (_ : 0<lam) (_ : 0<r)
    (ha:a∈grid D r) :
    (∑ i,if a≤point D r i then weights D lam r i else 0)=tail lam r a := by
  let j:=((grid D r).orderIsoOfFin rfl).symm ⟨a,ha⟩
  have he:point D r j=a := congrArg Subtype.val (((grid D r).orderIsoOfFin rfl).apply_symm_apply _)
  have hiff (i : Fin (grid D r).card) : a≤point D r i ↔ j.val ≤ i.val := by
    rw [←he]
    exact (point_mono D r).le_iff_le
  simp_rw [hiff]
  have hh:=probability_living (survival D lam r) (grid D r).card j.val j.isLt.le
  change (∑ i,if j.val ≤ i.val then weight (survival D lam r) i else 0)=_
  unfold FiniteSurvival.probability at hh
  simp only [survival_last,sub_zero,survival_fin,he] at hh
  convert hh using 1
  apply sum_congr rfl
  intro i _
  by_cases hi : j.val ≤ i.val <;> simp [hi]

end KServer.FiniteRadius

end


/-! Finite realization of the uniform heavy-ball radii. The finite grid
preserves every relevant metric threshold, hence its law is exact for balls. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteUniform
open FiniteRadius FiniteSurvival
attribute [local instance] Classical.propDecidable Classical.decEq

def tail (r a : ℝ) : ℝ := max 0 (min 1 ((2*r-a)/r))

lemma tail_nonneg (r a : ℝ) : 0 ≤ tail r a := le_max_left _ _
lemma tail_le_one (r a : ℝ) : tail r a ≤ 1 := max_le (by norm_num) (min_le_left _ _)
lemma tail_of_le {r a : ℝ} (hr : 0<r) (ha : a≤r) : tail r a=1 := by
  have hh : 1≤(2*r-a)/r := (le_div_iff₀ hr).mpr (by linarith)
  simp [tail,min_eq_left hh]
lemma tail_of_ge {r a : ℝ} (hr : 0<r) (ha : 2*r≤a) : tail r a=0 := by
  have hh : (2*r-a)/r≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le
  simp [tail,min_eq_right (by linarith : (2*r-a)/r≤1),max_eq_left hh]
lemma tail_antitone {r : ℝ} (hr : 0<r) : Antitone (tail r) := by
  intro a b hab
  exact max_le_max_left _ (min_le_min_left _ (div_le_div_of_nonneg_right (by linarith) hr.le))
lemma tail_lipschitz {r a b : ℝ} (hr : 0<r) : |tail r a-tail r b|≤|a-b|/r := by
  have h1 := abs_max_sub_max_le_max (0:ℝ) (min 1 ((2*r-a)/r)) 0 (min 1 ((2*r-b)/r))
  have h2 := abs_min_sub_min_le_max (1:ℝ) ((2*r-a)/r) 1 ((2*r-b)/r)
  simp only [sub_self,abs_zero] at h1 h2
  have h1' := h1.trans (max_le (abs_nonneg _) le_rfl)
  have h2' := h2.trans (max_le (abs_nonneg _) le_rfl)
  have he : (2*r-a)/r-(2*r-b)/r=-(a-b)/r := by ring
  simpa only [tail,he,abs_div,abs_neg,abs_of_pos hr] using h1'.trans h2'

def survival (D : Finset ℝ) (r : ℝ) (a : ℕ) : ℝ :=
  if ha:a<(grid D r).card then tail r (point D r ⟨a,ha⟩) else 0
lemma survival_fin (D : Finset ℝ) (r : ℝ) (a : Fin (grid D r).card) :
    survival D r a=tail r (point D r a) := by simp [survival,a.isLt]
lemma survival_zero (D : Finset ℝ) {r : ℝ} (hr : 0<r) : survival D r 0=1 := by
  rw [survival,dite_eq_left (grid_pos D r),point_zero D hr]
  exact tail_of_le hr le_rfl
lemma survival_last (D : Finset ℝ) (r : ℝ) : survival D r (grid D r).card=0 := by simp [survival]
lemma survival_nonneg (D : Finset ℝ) (r : ℝ) (a : ℕ) : 0 ≤ survival D r a := by
  unfold survival; split_ifs
  · exact tail_nonneg _ _
  · rfl
lemma survival_antitone (D : Finset ℝ) {r : ℝ} (hr : 0<r) : Antitone (survival D r) := by
  intro a b hab
  by_cases hb:b<(grid D r).card
  · have ha:a<(grid D r).card := lt_of_le_of_lt hab hb
    rw [survival,dite_eq_left hb,survival,dite_eq_left ha]
    exact tail_antitone hr ((point_mono D r).monotone hab)
  · rw [survival,dite_eq_right hb]
    exact survival_nonneg D r a

def weights (D : Finset ℝ) (r : ℝ) (i : Fin (grid D r).card) : ℝ := weight (survival D r) i
lemma weights_nonneg (D : Finset ℝ) {r : ℝ} (hr : 0<r) (i : Fin (grid D r).card) :
    0≤weights D r i := weight_nonneg (survival_antitone D hr) i
lemma weights_sum (D : Finset ℝ) {r : ℝ} (hr : 0<r) : ∑ i,weights D r i=1 := by
  change (∑ i : Fin (grid D r).card,weight (survival D r) i)=1
  rw [weight_sum,survival_zero D hr,survival_last]
  norm_num
lemma grid_tail (D : Finset ℝ) {r a : ℝ} (ha:a∈grid D r) :
    (∑ i,if a≤point D r i then weights D r i else 0)=tail r a := by
  let j:=((grid D r).orderIsoOfFin rfl).symm ⟨a,ha⟩
  have he:point D r j=a := congrArg Subtype.val (((grid D r).orderIsoOfFin rfl).apply_symm_apply _)
  have hiff (i : Fin (grid D r).card) : a≤point D r i ↔ j.val ≤ i.val := by
    rw [←he]
    exact (point_mono D r).le_iff_le
  simp_rw [hiff]
  have hh:=probability_living (survival D r) (grid D r).card j.val j.isLt.le
  change (∑ i,if j.val ≤ i.val then weight (survival D r) i else 0)=_
  unfold FiniteSurvival.probability at hh
  simp only [survival_last,sub_zero,survival_fin,he] at hh
  convert hh using 1
  apply sum_congr rfl
  intro i _
  by_cases hi : j.val ≤ i.val <;> simp [hi]
lemma query_tail (D : Finset ℝ) {r a : ℝ} (hr : 0<r) (ha:a∈D) :
    (∑ i,if a≤point D r i then weights D r i else 0)=tail r a := by
  by_cases hlo : a<r
  · rw [tail_of_le hr hlo.le]
    convert weights_sum D hr using 1
    apply sum_congr rfl
    intro i _
    exact ite_eq_left (hlo.le.trans (point_range D hr i).1)
  · by_cases hhi : 2*r<a
    · rw [tail_of_ge hr hhi.le]
      apply sum_eq_zero
      intro i _
      exact ite_eq_right (not_le.mpr ((point_range D hr i).2.trans_lt hhi))
    · exact grid_tail D (mem_insert_of_mem (mem_insert_of_mem
        (mem_filter.mpr ⟨ha,le_of_not_gt hlo,le_of_not_gt hhi⟩)))

variable {Y : Type*} [Fintype Y] [PseudoMetricSpace Y]
def thresholds (r : ℝ) : Finset ℝ := univ.image (fun p : Y×Y=>(dist p.1 p.2-12*r)/4)
lemma dist_threshold (r : ℝ) (x y : Y) : (dist x y-12*r)/4∈thresholds (Y:=Y) r :=
  mem_image.mpr ⟨(x,y),mem_univ _,rfl⟩
abbrev Outcome (Y : Type*) [Fintype Y] [PseudoMetricSpace Y] (r : ℝ) := Fin (grid (thresholds (Y:=Y) r) r).card
def radius (r : ℝ) (i : Outcome Y r) : ℝ := 4*point (thresholds (Y:=Y) r) r i+12*r
def law (r : ℝ) (i : Outcome Y r) : ℝ := weights (thresholds (Y:=Y) r) r i
lemma radius_range {r : ℝ} (hr : 0<r) (i : Outcome Y r) : radius r i∈Set.Icc (16*r) (20*r) := by
  have hh:=point_range (thresholds (Y:=Y) r) hr i
  dsimp [radius]; constructor <;> linarith [hh.1,hh.2]
lemma law_nonneg {r : ℝ} (hr : 0<r) (i : Outcome Y r) : 0≤law r i := weights_nonneg _ hr i
lemma law_sum {r : ℝ} (hr : 0<r) : (∑ i : Outcome Y r,law r i)=1 := weights_sum _ hr
lemma ball_probability {r : ℝ} (hr : 0<r) (c x : Y) :
    (∑ i : Outcome Y r,if dist c x≤radius r i then law r i else 0)=tail r ((dist c x-12*r)/4) := by
  convert query_tail (thresholds (Y:=Y) r) hr (dist_threshold r c x) using 1
  apply sum_congr rfl
  intro i _
  have he : dist c x≤radius r i ↔ (dist c x-12*r)/4≤point (thresholds (Y:=Y) r) r i := by
    dsimp [radius]; constructor <;> intro hh <;> linarith
  simp only [he,law]

def separates (r : ℝ) (c x y : Y) (i : Outcome Y r) : Prop :=
  (dist c x≤radius r i ∧ radius r i<dist c y) ∨
  (dist c y≤radius r i ∧ radius r i<dist c x)
lemma separates_comm (r : ℝ) (c x y : Y) (i : Outcome Y r) :
    separates r c x y i ↔ separates r c y x i := Or.comm
lemma separation_ordered {r : ℝ} (hr : 0<r) (c x y : Y) (hxy : dist c x≤dist c y) :
    (∑ i : Outcome Y r,if separates r c x y i then law r i else 0)=
      tail r ((dist c x-12*r)/4)-tail r ((dist c y-12*r)/4) := by
  rw [←ball_probability hr c x,←ball_probability hr c y,←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hy : dist c y≤radius r i
  · have hx:=hxy.trans hy
    simp [separates,hy,hx,not_lt_of_ge hx,not_lt_of_ge hy]
  · have hny:=lt_of_not_ge hy
    by_cases hx : dist c x≤radius r i <;> simp [separates,hy,hx,hny]

theorem one_ball_bound {r : ℝ} (hr : 0<r) (c x y : Y) :
    (∑ i : Outcome Y r,if separates r c x y i then law r i else 0)≤dist x y/(4*r) := by
  wlog hxy : dist c x≤dist c y generalizing x y
  · have hb:=this y x (le_of_not_ge hxy)
    have he : (fun i : Outcome Y r=>separates r c x y i)=(fun i=>separates r c y x i) := by
      funext i; exact propext (separates_comm r c x y i)
    simpa only [he,dist_comm y x] using hb
  rw [separation_ordered hr c x y hxy]
  have hLip:=tail_lipschitz (a:=(dist c x-12*r)/4) (b:=(dist c y-12*r)/4) hr
  have he : (dist c x-12*r)/4-(dist c y-12*r)/4=(dist c x-dist c y)/4 := by ring
  rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)] at hLip
  have hdist : |dist c x-dist c y|≤dist x y := by
    simpa only [dist_comm c x,dist_comm c y] using abs_dist_sub_le x y c
  calc _ ≤ |tail r ((dist c x-12*r)/4)-tail r ((dist c y-12*r)/4)| := le_abs_self _
    _ ≤ (|dist c x-dist c y|/4)/r := hLip
    _ = |dist c x-dist c y|/(4*r) := by ring
    _ ≤ dist x y/(4*r) := div_le_div_of_nonneg_right hdist (by positivity)
end KServer.FiniteUniform

end


/-! The literal causal heavy-ball radii/labels recursion on the constructed
finite tape. The center schedule is the actual true-prefix pilot schedule. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HeavySchedule
open HeavyCenters HeavyLabels FiniteExperiment
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MetricSpace Y] [Fintype Y]
variable {k H : ℕ} [NeZero k]

structure Data (Y : Type*) [Fintype Y] where
  rad : Y → ℝ
  label : Y → Pool Y
  previous : Y → Pool Y

def initial (Y : Type*) [Fintype Y] (r : ℝ) : Data Y :=
  ⟨fun _=>16*r,fun _=>⟨0,by omega⟩,fun _=>⟨0,by omega⟩⟩

def run (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y)) (r γ δ : ℝ)
    (σ : Fin H → Y) (tape : Fin H → FiniteUniform.Outcome Y r) : ℕ → Data Y
  | 0 => initial Y r
  | t+1 =>
    let old:=run s law r γ δ σ tape t
    if ht:t<H then
      let x:=σ ⟨t,ht⟩
      let C:=centers s law r γ δ σ t
      if Active r γ δ C (mu s law (t+1) σ) x then
        let R:=FiniteUniform.radius r (tape ⟨t,ht⟩)
        ⟨Function.update old.rad x R,
          updatedLabel C (centers s law r γ δ σ (t-1)) old.rad old.label old.previous x R,
          old.label⟩
      else ⟨old.rad,old.label,old.label⟩
    else ⟨old.rad,old.label,old.label⟩

lemma run_valid (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {r : ℝ} (hr : 0<r) (γ δ : ℝ) (σ : Fin H → Y) (tape : Fin H → FiniteUniform.Outcome Y r)
    (t : ℕ) :
    (∀ a∈centers s law r γ δ σ t,(run s law r γ δ σ tape t).rad a∈Set.Icc (16*r) (20*r)) ∧
    Set.InjOn (run s law r γ δ σ tape t).label (centers s law r γ δ σ t:Set Y) := by
  induction t with
  | zero => simp [centers,Set.InjOn]
  | succ t ih =>
    rw [run,centers]
    dsimp only
    simp only [HeavyCenters.step]
    split_ifs with ht ha
    · constructor
      · intro a haC
        rcases mem_insert.mp haC with hax|haC
        · subst a
          simpa only [Function.update_self] using FiniteUniform.radius_range hr (tape ⟨t,ht⟩)
        · have hax : a≠σ ⟨t,ht⟩ := by
            intro he
            have hd:=(mem_filter.mp haC).2
            rw [he,dist_self] at hd
            linarith
          simp only [Function.update_of_ne hax]
          exact ih.1 a (mem_filter.mp haC).1
      · have hv := update_injective (D := centers s law r γ δ σ (t-1))
          (prev := (run s law r γ δ σ tape t).previous) (x := σ ⟨t,ht⟩)
          hr (fun a ha=>(ih.1 a ha).2) (FiniteUniform.radius_range hr (tape ⟨t,ht⟩)).2 ih.2
        exact hv
    · exact ih
    · exact ih

def birth (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y)) (r γ δ : ℝ)
    (σ : Fin H → Y) : ℕ → Y → Option (Fin H)
  | 0 => fun _=>none
  | t+1 => if ht:t<H then
      if Active r γ δ (centers s law r γ δ σ t) (mu s law (t+1) σ) (σ ⟨t,ht⟩)
      then Function.update (birth s law r γ δ σ t) (σ ⟨t,ht⟩) (some ⟨t,ht⟩)
      else birth s law r γ δ σ t
    else birth s law r γ δ σ t

lemma radius_birth (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y)) (r γ δ : ℝ)
    (σ : Fin H → Y) (tape : Fin H → FiniteUniform.Outcome Y r) (t : ℕ) (a : Y) :
    (run s law r γ δ σ tape t).rad a=
      match birth s law r γ δ σ t a with
      | none=>16*r
      | some i=>FiniteUniform.radius r (tape i) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run,birth]
    dsimp only
    split_ifs with ht ha
    · by_cases hx : a=σ ⟨t,ht⟩
      · subst a; simp only [Function.update_self]
      · simp only [Function.update_of_ne hx]; exact ih
    · exact ih
    · exact ih

lemma present_birth (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {r : ℝ} (hr : 0<r) (γ δ : ℝ) (σ : Fin H → Y) (t : ℕ) (a : Y)
    (ha : a∈centers s law r γ δ σ t) :
    ∃ i : Fin H,birth s law r γ δ σ t a=some i ∧ i.val<t ∧ σ i=a := by
  induction t with
  | zero => simp [centers] at ha
  | succ t ih =>
    rw [centers] at ha
    simp only [HeavyCenters.step] at ha
    rw [birth]
    split_ifs at * with ht hA
    · rcases mem_insert.mp ha with he|ha
      · subst a
        exact ⟨⟨t,ht⟩,Function.update_self _ _ _,by change t<t+1; omega,rfl⟩
      · have hx : a≠σ ⟨t,ht⟩ := by
          intro he
          have hd:=(mem_filter.mp ha).2
          rw [he,dist_self] at hd
          linarith
        obtain ⟨i,hi,hb,hc⟩:=ih (mem_filter.mp ha).1
        exact ⟨i,by simpa only [Function.update_of_ne hx] using hi,by omega,hc⟩
    · obtain ⟨i,hi,hb,hc⟩:=ih ha
      exact ⟨i,hi,by omega,hc⟩
    · obtain ⟨i,hi,hb,hc⟩:=ih ha
      exact ⟨i,hi,by omega,hc⟩
end KServer.HeavySchedule

end


/-! Exact finite ball laws for the metric thresholds used in §07.  Their
chronological first-hit estimate uses the constructed product law, not an
independence premise about a posterior filtration. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteBallLaw
open PartitionProbabilities FiniteRadius
attribute [local instance] Classical.propDecidable Classical.decEq

lemma query_tail (D : Finset ℝ) {lam r a : ℝ} (hlam : 0 < lam) (hr : 0 < r)
    (ha : a ∈ D) :
    (∑ i, if a ≤ point D r i then weights D lam r i else 0)=tail lam r a := by
  by_cases hlo : a < r
  · rw [tail_of_le hlam hr hlo.le]
    convert weights_sum D hlam hr using 1
    apply sum_congr rfl
    intro i _
    exact ite_eq_left (hlo.le.trans (point_range D hr i).1)
  · by_cases hhi : 2*r < a
    · rw [tail_of_ge hr hhi.le]
      apply sum_eq_zero
      intro i _
      exact ite_eq_right (not_le.mpr ((point_range D hr i).2.trans_lt hhi))
    · apply grid_tail D hlam hr
      exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨ha,le_of_not_gt hlo,le_of_not_gt hhi⟩))

variable {Y : Type*} [Fintype Y] [PseudoMetricSpace Y]

def thresholds : Finset ℝ := univ.image (fun p : Y×Y => dist p.1 p.2)

lemma dist_threshold (x y : Y) : dist x y ∈ thresholds (Y:=Y) :=
  mem_image.mpr ⟨(x,y),mem_univ _,rfl⟩

abbrev Outcome (Y : Type*) [Fintype Y] [PseudoMetricSpace Y] (r : ℝ) :=
  Fin (grid (thresholds (Y:=Y)) r).card

def radius (r : ℝ) (i : Outcome Y r) : ℝ := point (thresholds (Y:=Y)) r i

def law (lam r : ℝ) (i : Outcome Y r) : ℝ := weights (thresholds (Y:=Y)) lam r i

lemma law_nonneg {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) (i : Outcome Y r) :
    0 ≤ law lam r i := weights_nonneg _ hlam hr i

lemma law_sum {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) :
    (∑ i : Outcome Y r, law lam r i)=1 := weights_sum _ hlam hr

lemma radius_range {r : ℝ} (hr : 0 < r) (i : Outcome Y r) : radius r i ∈ Set.Icc r (2*r) :=
  point_range _ hr i

lemma ball_probability {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) (c x : Y) :
    (∑ i : Outcome Y r, if dist c x ≤ radius r i then law lam r i else 0)=
      tail lam r (dist c x) := query_tail _ hlam hr (dist_threshold c x)

def hit (r : ℝ) (c x y : Y) (i : Outcome Y r) : Prop :=
  dist c x ≤ radius r i ∨ dist c y ≤ radius r i

def separates (r : ℝ) (c x y : Y) (i : Outcome Y r) : Prop :=
  (dist c x ≤ radius r i ∧ radius r i < dist c y) ∨
  (dist c y ≤ radius r i ∧ radius r i < dist c x)

lemma separation_hit (r : ℝ) (c x y : Y) (i : Outcome Y r) : separates r c x y i → hit r c x y i := by
  rintro (h|h)
  · exact Or.inl h.1
  · exact Or.inr h.1

lemma hit_min (r : ℝ) (c x y : Y) (i : Outcome Y r) :
    hit r c x y i ↔ min (dist c x) (dist c y) ≤ radius r i := by
  exact min_le_iff.symm

lemma separation_interval (r : ℝ) (c x y : Y) (i : Outcome Y r) :
    separates r c x y i ↔ min (dist c x) (dist c y) ≤ radius r i ∧
      radius r i < max (dist c x) (dist c y) := by
  rcases le_total (dist c x) (dist c y) with h|h
  · rw [min_eq_left h,max_eq_right h]
    constructor
    · rintro (he|he)
      · exact he
      · exact False.elim ((not_lt_of_ge (h.trans he.1)) he.2)
    · exact Or.inl
  · rw [min_eq_right h,max_eq_left h]
    constructor
    · rintro (he|he)
      · exact False.elim ((not_lt_of_ge (h.trans he.1)) he.2)
      · exact he
    · exact Or.inr

lemma min_threshold (c x y : Y) : min (dist c x) (dist c y) ∈ thresholds (Y:=Y) := by
  rcases le_total (dist c x) (dist c y) with h|h
  · simpa [min_eq_left h] using dist_threshold c x
  · simpa [min_eq_right h] using dist_threshold c y

lemma max_threshold (c x y : Y) : max (dist c x) (dist c y) ∈ thresholds (Y:=Y) := by
  rcases le_total (dist c x) (dist c y) with h|h
  · simpa [max_eq_right h] using dist_threshold c y
  · simpa [max_eq_left h] using dist_threshold c x

lemma hit_probability {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) (c x y : Y) :
    (∑ i : Outcome Y r, if hit r c x y i then law lam r i else 0)=
      tail lam r (min (dist c x) (dist c y)) := by
  simp_rw [hit_min]
  exact query_tail _ hlam hr (min_threshold c x y)

lemma separation_probability {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) (c x y : Y) :
    (∑ i : Outcome Y r, if separates r c x y i then law lam r i else 0)=
      tail lam r (min (dist c x) (dist c y))-
        tail lam r (max (dist c x) (dist c y)) := by
  rw [←query_tail _ hlam hr (min_threshold c x y),←query_tail _ hlam hr (max_threshold c x y),←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [separation_interval]
  simp only [radius,law]
  by_cases h : max (dist c x) (dist c y) ≤ point (thresholds (Y:=Y)) r i
  · have hl : min (dist c x) (dist c y) ≤ point (thresholds (Y:=Y)) r i := (min_le_max).trans h
    simp [h,hl,not_lt_of_ge h]
  · have hh : point (thresholds (Y:=Y)) r i < max (dist c x) (dist c y) := lt_of_not_ge h
    simp only [hh,and_true,ite_eq_right h,sub_zero]

omit [Fintype Y] in
lemma width_distance (c x y : Y) : max (dist c x) (dist c y)-min (dist c x) (dist c y) ≤ dist x y := by
  rw [max_sub_min_eq_abs]
  simpa [dist_comm,abs_sub_comm] using abs_dist_sub_le x y c

lemma one_ball_bound {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r) (c x y : Y) :
    (∑ i : Outcome Y r, if separates r c x y i then law lam r i else 0) ≤
      (lam*dist x y/r)*((∑ i : Outcome Y r, if hit r c x y i then law lam r i else 0)+
        1/(Real.exp lam-1)) := by
  rw [separation_probability hlam hr,hit_probability hlam hr]
  have ht := tail_interval_bound hlam hr (min_le_max (a:=dist c x) (b:=dist c y))
  refine ht.trans ?_
  apply mul_le_mul_of_nonneg_right
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (width_distance c x y) hlam.le) hr.le
  · exact add_nonneg (tail_range hlam _ _).1 (div_nonneg zero_le_one (by linarith [Real.one_lt_exp_iff.mpr hlam]))

/-- The finite radius tape realizes the exact source truncated-exponential
first-hit bound for any fixed chronological list of present candidates. -/
theorem chronological_bound {n : ℕ} {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r)
    (centers : Fin n → Y) (x y : Y) :
    probability (fun _ : Fin n => law (Y:=Y) lam r)
      (firstSeparation (fun j => hit r (centers j) x y) (fun j => separates r (centers j) x y)) ≤
      (lam*dist x y/r)*(1+(1/(Real.exp lam-1))*n) := by
  apply independent_first_hit_bound
  · exact fun _ => law_nonneg hlam hr
  · exact fun _ => law_sum hlam hr
  · exact fun j => separation_hit r (centers j) x y
  · positivity
  · exact div_nonneg zero_le_one (by linarith [Real.one_lt_exp_iff.mpr hlam])
  · exact fun j => one_ball_bound hlam hr (centers j) x y

lemma lambda_pos {K : ℕ} (hK : 1 ≤ K) : 0 < Real.log (1+(K:ℝ)^2) := by
  have hk : (1:ℝ) ≤ K := by exact_mod_cast hK
  apply Real.log_pos
  nlinarith

/-- With at most K² potentially hitting records the chronological estimate is
2λd/r, independent of the total number of previous insertions. -/
theorem bounded_roster {n K : ℕ} (hK : 1 ≤ K) (hn : n ≤ K^2) {r : ℝ} (hr : 0 < r)
    (centers : Fin n → Y) (x y : Y) :
    probability (fun _ : Fin n => law (Y:=Y) (Real.log (1+(K:ℝ)^2)) r)
      (firstSeparation (fun j => hit r (centers j) x y) (fun j => separates r (centers j) x y)) ≤
      2*Real.log (1+(K:ℝ)^2)*dist x y/r := by
  have hl := lambda_pos hK
  refine (chronological_bound hl hr centers x y).trans ?_
  have hk : (0:ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hn' : (n:ℝ) ≤ (K:ℝ)^2 := by exact_mod_cast hn
  rw [Real.exp_log (by positivity : 0 < 1+(K:ℝ)^2),add_sub_cancel_left]
  have hfrac : (1/(K:ℝ)^2)*(n:ℝ) ≤ 1 := by
    rw [one_div,mul_comm,←div_eq_mul_inv]
    exact (div_le_one (sq_pos_of_pos hk)).mpr hn'
  have hc : 0 ≤ Real.log (1+(K:ℝ)^2)*dist x y/r := by positivity
  calc _ ≤ (Real.log (1+(K:ℝ)^2)*dist x y/r)*2 :=
      mul_le_mul_of_nonneg_left (by linarith) hc
    _ = _ := by ring

end KServer.FiniteBallLaw

end


/- Chronological rosters retain insertion times rather than surviving random balls. The tests are independent of the partition tape, and young records reserve slots. -/


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Chronological

variable {Y : Type*} [MetricSpace Y]

/-- Number of later insertions in the fixed-radius neighbourhood of an entry. -/
def age (center : ℕ → Y) (I : Finset ℕ) (R : ℝ) (i : ℕ) : ℕ := by
  classical
  exact (I.filter fun j => i < j ∧ dist (center i) (center j) ≤ R).card

/-- Chronological, not surviving, entries below an age cutoff. -/
def young (center : ℕ → Y) (I : Finset ℕ) (R : ℝ) (A : ℕ) : Finset ℕ := by
  classical
  exact I.filter fun i => age center I R i < A

lemma mem_young (center : ℕ → Y) (I : Finset ℕ) (R : ℝ) (A i : ℕ) :
    i ∈ young center I R A ↔ i ∈ I ∧ age center I R i < A := by
  classical
  simp [young]

lemma age_mono (center : ℕ → Y) {I J : Finset ℕ} {R S : ℝ} (hIJ : I ⊆ J)
    (hRS : R ≤ S) (i : ℕ) : age center I R i ≤ age center J S i := by
  classical
  apply card_le_card
  intro j hj
  obtain ⟨hj,hij,hd⟩ := mem_filter.mp hj
  exact mem_filter.mpr ⟨hIJ hj,hij,hd.trans hRS⟩

/-- Adding the next insertion increments precisely neighbouring old entries. -/
lemma age_insert (center : ℕ → Y) (I : Finset ℕ) (R : ℝ) {i t : ℕ}
    (ht : t ∉ I) (hit : i < t) :
    age center (insert t I) R i = age center I R i +
      if dist (center i) (center t) ≤ R then 1 else 0 := by
  classical
  unfold age
  rw [filter_insert]
  by_cases hd : dist (center i) (center t) ≤ R
  · rw [ite_eq_left ⟨hit, hd⟩, ite_eq_left hd,
      card_insert_of_notMem (fun hm => ht (mem_filter.mp hm).1)]
  · rw [ite_eq_right (fun h => hd h.2), ite_eq_right hd]
    simp

lemma age_new (center : ℕ → Y) (I : Finset ℕ) (R : ℝ) {t : ℕ}
    (ht : ∀ i ∈ I, i < t) : age center (insert t I) R t = 0 := by
  classical
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨hi,hti,_⟩ := mem_filter.mp hi
  rcases mem_insert.mp hi with rfl | hi
  · omega
  · have := ht i hi
    omega

/-- Actual age-count lemma. No independence or surviving-record assumption is
used, and repeated centers are allowed. -/
theorem local_age_count (center : ℕ → Y) (I S : Finset ℕ) (R : ℝ) (A : ℕ)
    (hSI : S ⊆ I) (hyoung : ∀ i ∈ S, age center I R i < A)
    (hdiam : ∀ i ∈ S, ∀ j ∈ S, dist (center i) (center j) ≤ R) :
    S.card ≤ A := by
  classical
  by_cases hS : S.Nonempty
  · let i := S.min' hS
    have hi : i ∈ S := min'_mem _ _
    have hcover : S.erase i ⊆ I.filter (fun j => i < j ∧ dist (center i) (center j) ≤ R) := by
      intro j hj
      obtain ⟨hji,hj⟩ := mem_erase.mp hj
      refine mem_filter.mpr ⟨hSI hj,?_,hdiam i hi j hj⟩
      have hij := min'_le S j hj
      change i ≤ j at hij
      omega
    have hb := card_le_card hcover
    change (S.erase i).card ≤ age center I R i at hb
    have he := card_erase_add_one hi
    have ha := hyoung i hi
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

/-- The exact test in the manuscript. Its input is a qualifying request,
not a condition involving lifetimes, radii, allocation, or rounding. -/
def insertTest (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (K t : ℕ)
    (qualifies : Prop) : Prop :=
  qualifies ∧ ¬ ∃ i ∈ I, age center I (20*r) i < K ∧ dist (center i) (center t) ≤ r/2

/-- Chronological insertion history after `t` requests. `qualifies` will be
computed from the actual true-prefix posterior and the fixed tier parameter. -/
def schedule (request : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop) : ℕ → Finset ℕ
  | 0 => ∅
  | t+1 => by
      classical
      let I := schedule request r K qualifies t
      exact if insertTest request I r K t (qualifies t) then insert t I else I

lemma schedule_before (request : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop)
    (t : ℕ) : ∀ i ∈ schedule request r K qualifies t, i < t := by
  classical
  induction t with
  | zero => simp [schedule]
  | succ t ih =>
      intro i hi
      simp only [schedule] at hi
      split_ifs at hi with h
      · rcases mem_insert.mp hi with rfl | hi
        · omega
        · exact (ih i hi).trans (Nat.lt_succ_self t)
      · exact (ih i hi).trans (Nat.lt_succ_self t)

lemma qualified_coverage (request : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop)
    (t : ℕ) (hK : 0 < K) (hr : 0 ≤ r) (hq : qualifies t) :
    ∃ i ∈ schedule request r K qualifies (t+1),
      age request (schedule request r K qualifies (t+1)) (20*r) i < K ∧
      dist (request i) (request t) ≤ r/2 := by
  classical
  let I := schedule request r K qualifies t
  by_cases ht : insertTest request I r K t (qualifies t)
  · have he : schedule request r K qualifies (t+1) = insert t I := by
      simp only [schedule]
      exact ite_eq_left ht
    rw [he]
    refine ⟨t, mem_insert_self _ _, ?_, ?_⟩
    · rw [age_new request I (20*r) (schedule_before request r K qualifies t)]
      exact hK
    · simp only [dist_self]
      positivity
  · have he : schedule request r K qualifies (t+1) = I := by
      simp only [schedule]
      exact ite_eq_right ht
    rw [he]
    have hh : ∃ i ∈ I, age request I (20*r) i < K ∧ dist (request i) (request t) ≤ r/2 := by
      by_contra hn
      exact ht ⟨hq,hn⟩
    exact hh

/-- Reservation count for the complete chronological roster, by applying the
local bound separately to each center in the finite metric. -/
theorem reserved_count [Fintype Y] (center : ℕ → Y) (I : Finset ℕ) {R : ℝ}
    (hR : 0 ≤ R) (A : ℕ) : (young center I R A).card ≤ Fintype.card Y * A := by
  classical
  let S := young center I R A
  have hlocal (y : Y) : (S.filter fun i => center i = y).card ≤ A := by
    apply local_age_count center I _ R A
    · intro i hi
      exact ((mem_young center I R A i).mp (mem_filter.mp hi).1).1
    · intro i hi
      exact ((mem_young center I R A i).mp (mem_filter.mp hi).1).2
    · intro i hi j hj
      have hi' := (mem_filter.mp hi).2
      have hj' := (mem_filter.mp hj).2
      rw [hi',hj',dist_self]
      exact hR
  calc S.card = ∑ y : Y, (S.filter fun i => center i = y).card := by
        symm
        simpa using sum_card_fiberwise_eq_card_filter S univ center
       _ ≤ ∑ _y : Y, A := sum_le_sum fun y _ => hlocal y
       _ = Fintype.card Y * A := by simp

end KServer.Chronological

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.SparseFirstHit
open PartitionProbabilities FiniteBallLaw Chronological
attribute [local instance] Classical.propDecidable Classical.decEq

/-- An error is paid only on indices that can hit a queried point.  This
permits a preallocated horizon-size tape without a horizon-size bound. -/
theorem sparse_bound {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)]
    {hit sep : ∀ i, Ω i → Prop} (w : ∀ i, Ω i → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a=1)
    (hsep : ∀ i a, sep i a → hit i a) {c : ℝ} (ε : Fin n → ℝ)
    (hc : 0 ≤ c) (hε : ∀ i, 0 ≤ ε i)
    (hm : ∀ i, (∑ a, if sep i a then w i a else 0) ≤
      c*((∑ a, if hit i a then w i a else 0)+ε i)) :
    probability w (firstSeparation hit sep) ≤ c*(1+∑ i, ε i) := by
  let p : Fin n → ℝ := fun i => ∑ a, if hit i a then w i a else 0
  have hp (i : Fin n) : p i ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨sum_nonneg (fun a _ => ?_), ?_⟩
    · split_ifs
      · exact hw i a
      · rfl
    · calc p i ≤ ∑ a, w i a := by
             apply sum_le_sum
             intro a _
             split_ifs
             · rfl
             · exact hw i a
           _ = 1 := hw1 i
  let q : Fin n → ℝ := fun i => ∏ j ∈ univ.filter (fun j : Fin n => j < i), (1-p j)
  have hq (i : Fin n) : q i ∈ Set.Icc (0:ℝ) 1 := by
    exact ⟨prod_nonneg (fun j _ => sub_nonneg.mpr (hp j).2),
      prod_le_one₀ (fun index _ => sub_nonneg.mpr (hp index).2)
        (fun index _ => by linarith [(hp index).1])⟩
  have hb (i : Fin n) : probability w (firstAt hit sep i) ≤
      c*(probability w (firstAt hit hit i)+ε i) := by
    rw [firstAt_probability w hw1,firstAt_probability w hw1]
    change (∑ a, if sep i a then w i a else 0)*q i ≤ c*(p i*q i+ε i)
    calc _ ≤ (c*(p i+ε i))*q i := mul_le_mul_of_nonneg_right (hm i) (hq i).1
         _ ≤ _ := by nlinarith only [mul_nonneg hc (mul_nonneg (hε i) (by linarith [(hq i).2] : 0 ≤ 1-q i))]
  calc probability w (firstSeparation hit sep) = ∑ i, probability w (firstAt hit sep i) :=
         firstSeparation_probability hsep w
       _ ≤ ∑ i, c*(probability w (firstAt hit hit i)+ε i) := sum_le_sum (fun i _ => hb i)
       _ = c*(probability w (firstSeparation hit hit)+∑ i, ε i) := by
         rw [← mul_sum,sum_add_distrib,← firstSeparation_probability (fun _ _ h => h) w]
       _ ≤ c*(1+∑ i, ε i) := mul_le_mul_of_nonneg_left
         (add_le_add (probability_range hw hw1 _).2 le_rfl) hc

variable {Y : Type*} [Fintype Y] [MetricSpace Y] {H : ℕ}

def candidates (r : ℝ) (center : Fin H → Y) (present : Fin H → Prop) (x y : Y) : Finset (Fin H) :=
  univ.filter fun i => present i ∧ min (dist (center i) x) (dist (center i) y) ≤ 2*r

lemma absent_hit {r : ℝ} (hr : 0 < r) (c x y : Y) (d : Outcome Y r)
    (h : ¬min (dist c x) (dist c y) ≤ 2*r) : ¬hit r c x y d := by
  intro hh
  exact h ((hit_min _ _ _ _ _).mp hh |>.trans (radius_range hr d).2)

/-- All previous insertion ordinals, with nonpresent records literally
suppressed.  Only potential hitters contribute the truncation error. -/
theorem present_bound {lam r : ℝ} (hlam : 0 < lam) (hr : 0 < r)
    (center : Fin H → Y) (present : Fin H → Prop) (x y : Y) :
    probability (fun _ : Fin H => law (Y:=Y) lam r)
      (firstSeparation (fun j d => present j ∧ hit r (center j) x y d)
        (fun j d => present j ∧ separates r (center j) x y d)) ≤
      (lam*dist x y/r)*(1+(1/(Real.exp lam-1))*(candidates r center present x y).card) := by
  let ε : Fin H → ℝ := fun j => if j∈candidates r center present x y then 1/(Real.exp lam-1) else 0
  have heps : ∑ j, ε j=(1/(Real.exp lam-1))*(candidates r center present x y).card := by
    simp [ε,sum_ite_mem,mul_comm]
  rw [←heps]
  apply sparse_bound
  · exact fun _ => law_nonneg hlam hr
  · exact fun _ => law_sum hlam hr
  · exact fun j d h => ⟨h.1,separation_hit _ _ _ _ _ h.2⟩
  · positivity
  · intro j
    dsimp [ε]
    split_ifs
    · exact div_nonneg zero_le_one (by linarith [Real.one_lt_exp_iff.mpr hlam])
    · rfl
  · intro j
    by_cases hp : present j
    · simp only [hp,true_and]
      by_cases hd : min (dist (center j) x) (dist (center j) y) ≤ 2*r
      · have hm : j∈candidates r center present x y := mem_filter.mpr ⟨mem_univ _,hp,hd⟩
        simpa only [ε,ite_eq_left hm] using one_ball_bound hlam hr (center j) x y
      · have hhit (d : Outcome Y r) : ¬hit r (center j) x y d := absent_hit hr _ _ _ _ hd
        have hsep (d : Outcome Y r) : ¬separates r (center j) x y d := fun h=>hhit d (separation_hit _ _ _ _ _ h)
        have hm : j∉candidates r center present x y := fun hh => hd (mem_filter.mp hh).2.2
        simp [hhit,hsep,ε,hm]
    · simp [hp,ε,candidates]

omit [Fintype Y] in
lemma close_centers {r : ℝ} (hr : 0 ≤ r) {c d x y : Y} (hxy : dist x y ≤ r)
    (hc : min (dist c x) (dist c y) ≤ 2*r) (hd : min (dist d x) (dist d y) ≤ 2*r) :
    dist c d ≤ 20*r := by
  rcases min_le_iff.mp hc with hc|hc <;> rcases min_le_iff.mp hd with hd|hd
  · have ht := dist_triangle c x d
    rw [dist_comm x d] at ht
    linarith
  · have ht := dist_triangle4 c x y d
    rw [dist_comm y d] at ht
    linarith
  · have ht := dist_triangle4 c y x d
    rw [dist_comm y x,dist_comm x d] at ht
    linarith
  · have ht := dist_triangle c y d
    rw [dist_comm y d] at ht
    linarith

omit [Fintype Y] in
lemma candidate_count {r : ℝ} (hr : 0 ≤ r) (center : ℕ → Y) (I : Finset ℕ)
    (present : Fin H → Prop) {K : ℕ}
    (hp : ∀ i, present i → (i:ℕ)∈I ∧ age center I (20*r) i<K^2)
    (x y : Y) (hxy : dist x y ≤ r) :
    (candidates r (fun i : Fin H => center i) present x y).card ≤ K^2 := by
  let S : Finset (Fin H) := candidates r (fun i : Fin H => center i) present x y
  have hinj : Function.Injective (fun i : Fin H => (i:ℕ)) := Fin.val_injective
  have he : (S.image (fun i : Fin H => (i:ℕ))).card=S.card := card_image_of_injective _ hinj
  rw [←he]
  apply local_age_count center I _ (20*r) (K^2)
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact (hp i (mem_filter.mp hi).2.1).1
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact (hp i (mem_filter.mp hi).2.1).2
  · intro i hi j hj
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hi
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hj
    exact close_centers hr hxy (mem_filter.mp ha).2.2 (mem_filter.mp hb).2.2

/-- Conditional on any actual presence pattern, the horizon-size radius tape
has the stated K²-independent first-hit bound, by the literal age count. -/
theorem chronological_roster_bound {K : ℕ} (hK : 1 ≤ K) {r : ℝ} (hr : 0 < r)
    (center : ℕ → Y) (I : Finset ℕ) (present : Fin H → Prop)
    (hp : ∀ i, present i → (i:ℕ)∈I ∧ age center I (20*r) i<K^2)
    (x y : Y) (hxy : dist x y ≤ r) :
    probability (fun _ : Fin H => law (Y:=Y) (Real.log (1+(K:ℝ)^2)) r)
      (firstSeparation (fun j d => present j ∧ hit r (center j) x y d)
        (fun j d => present j ∧ separates r (center j) x y d)) ≤
      2*Real.log (1+(K:ℝ)^2)*dist x y/r := by
  have hl := lambda_pos hK
  refine (present_bound hl hr (fun i : Fin H=>center i) present x y).trans ?_
  have hk : (0:ℝ) < K := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hn : ((candidates r (fun i : Fin H=>center i) present x y).card:ℝ) ≤ (K:ℝ)^2 := by
    exact_mod_cast candidate_count hr.le center I present hp x y hxy
  rw [Real.exp_log (by positivity : 0 < 1+(K:ℝ)^2),add_sub_cancel_left]
  have hfrac : (1/(K:ℝ)^2)*((candidates r (fun i : Fin H=>center i) present x y).card:ℝ) ≤ 1 := by
    rw [one_div,mul_comm,←div_eq_mul_inv]
    exact (div_le_one (sq_pos_of_pos hk)).mpr hn
  have hc : 0 ≤ Real.log (1+(K:ℝ)^2)*dist x y/r := by positivity
  calc _ ≤ (Real.log (1+(K:ℝ)^2)*dist x y/r)*2 :=
      mul_le_mul_of_nonneg_left (by linarith) hc
    _ = _ := by ring

end KServer.SparseFirstHit

end


/-! The distinct actual and auxiliary lifetimes of §07.  These estimates are
uniform in the horizon and in every fixed chronological insertion schedule.
Compulsory-retirement tails are unconditional, as required by the source. -/
noncomputable section
open scoped BigOperators
namespace KServer.RosterLifetimes

/-- Survival through `N` independent retirement trials of rate `q`. -/
def survive (q : ℝ) (N : ℕ) : ℝ := (1-q)^N

lemma survive_range {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) (N : ℕ) :
    survive q N ∈ Set.Icc (0:ℝ) 1 := by
  refine ⟨pow_nonneg (by linarith [hq.2]) _, ?_⟩
  exact pow_le_one₀ (by linarith [hq.2]) (by linarith [hq.1])

lemma survive_mono {q : ℝ} (hq : q ∈ Set.Icc (0:ℝ) 1) : Antitone (survive q) := by
  intro M N hMN
  exact pow_le_pow_of_le_one (by linarith [hq.2]) (by linarith [hq.1]) hMN

lemma survive_exp {q : ℝ} (hq : q ≤ 1) (N : ℕ) :
    survive q N ≤ Real.exp (-(q*N)) := by
  calc (1-q)^N ≤ (Real.exp (-q))^N :=
        pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg q) N
       _ = Real.exp (-(q*N)) := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma cubic_decay {x : ℝ} (hx : 0 ≤ x) : x^3*Real.exp (-x) ≤ 6 := by
  have h := Real.pow_div_factorial_le_exp x hx 3
  norm_num at h
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-x))
  have he : Real.exp x*Real.exp (-x)=1 := by rw [← Real.exp_add]; simp
  rw [he] at hm
  linarith

/-- Explicit uniform version of K² exp(-(K-1))=O(1/K). -/
lemma actual_exponential_bound {x : ℝ} (hx : 2 ≤ x) :
    x^2*Real.exp (-(x-1)) ≤ 48/x := by
  have hp : 0 < x := by linarith
  rw [le_div_iff₀ hp]
  have hc := cubic_decay (x := x-1) (by linarith)
  have hpow : x^3 ≤ 8*(x-1)^3 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ x) (by linarith : x ≤ 2*(x-1)) 3
    nlinarith only [h]
  have hm := mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg (-(x-1)))
  nlinarith only [hc,hm]

/-- Explicit uniform auxiliary tail estimate. The denominator really is √K,
not K; the two tapes are never identified. -/
lemma short_exponential_bound {x : ℝ} (hx : 2 ≤ x) :
    x*Real.exp (-((x-1)/Real.sqrt x)) ≤ 48/Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hy : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hs : (Real.sqrt x)^2=x := Real.sq_sqrt hx0
  have hd : Real.sqrt x/2 ≤ (x-1)/Real.sqrt x := by
    rw [le_div_iff₀ hy]
    nlinarith only [hs,hx]
  have he : Real.exp (-((x-1)/Real.sqrt x)) ≤ Real.exp (-(Real.sqrt x/2)) :=
    Real.exp_le_exp.mpr (neg_le_neg hd)
  have hc := cubic_decay (x := Real.sqrt x/2) (by positivity)
  have hc' : (Real.sqrt x)^3*Real.exp (-(Real.sqrt x/2)) ≤ 48 := by
    nlinarith only [hc]
  rw [le_div_iff₀ hy]
  calc x*Real.exp (-((x-1)/Real.sqrt x))*Real.sqrt x ≤
        x*Real.exp (-(Real.sqrt x/2))*Real.sqrt x := by gcongr
       _ = (Real.sqrt x)^3*Real.exp (-(Real.sqrt x/2)) := by calc
         _ = (Real.sqrt x)^2*Real.exp (-(Real.sqrt x/2))*Real.sqrt x := by rw [hs]
         _ = _ := by ring
       _ ≤ 48 := hc'

/-- Actual lifetime: ages 0,...,K-1 certain, trials K,...,K²-1,
compulsory retirement at K². -/
def actualPresence (K a : ℕ) : ℝ :=
  if a<K then 1 else if a<K^2 then survive (1/K) (a-K+1) else 0

/-- Auxiliary short lifetime: a trial on each positive age increment,
compulsory retirement at K.  It does not define the actual partition. -/
def shortPresence (K a : ℕ) : ℝ :=
  if a<K then survive (1/Real.sqrt K) a else 0

lemma actual_guaranteed {K a : ℕ} (ha : a<K) : actualPresence K a=1 := by
  simp [actualPresence,ha]

lemma actual_cutoff {K a : ℕ} (ha : K^2 ≤ a) : actualPresence K a=0 := by
  have hK : K ≤ K^2 := by nlinarith [Nat.zero_le K]
  simp [actualPresence,not_lt.mpr (hK.trans ha),not_lt.mpr ha]

lemma short_new {K : ℕ} (hK : 0<K) : shortPresence K 0=1 := by
  simp [shortPresence,hK,survive]

lemma short_cutoff {K a : ℕ} (ha : K ≤ a) : shortPresence K a=0 := by
  simp [shortPresence,not_lt.mpr ha]

/-- The source unconditional actual-first-coverer retirement estimate,
including both stochastic and compulsory terms.  The factor K² is the
geometric roster count proved from chronological ages, not the total history. -/
theorem actual_retirement_bound (K : ℕ) (hK : 2 ≤ K) :
    1/(K:ℝ)+(K:ℝ)^2*survive (1/(K:ℝ)) (K^2-K) ≤ 49/(K:ℝ) := by
  have hKr : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hKp : (0:ℝ) < K := by linarith
  have hKK : K ≤ K^2 := by nlinarith
  have hcast : ((K^2-K : ℕ):ℝ)=(K:ℝ)^2-K := by rw [Nat.cast_sub hKK,Nat.cast_pow]
  have hs := survive_exp (q := 1/(K:ℝ)) ((div_le_one hKp).mpr (by linarith)) (K^2-K)
  rw [hcast] at hs
  have he : -(1/(K:ℝ)*((K:ℝ)^2-K)) = -((K:ℝ)-1) := by field_simp
  rw [he] at hs
  have hb := (mul_le_mul_of_nonneg_left hs (sq_nonneg (K:ℝ))).trans (actual_exponential_bound hKr)
  have hsum := add_le_add_left hb (1/(K:ℝ))
  convert hsum using 1 <;> first | rfl | ring

/-- The auxiliary ramp can increase by at most this amount; its complete
retirement calculation has a uniform 49/√K bound. -/
theorem short_retirement_bound (K : ℕ) (hK : 2 ≤ K) :
    1/Real.sqrt K+(K:ℝ)*survive (1/Real.sqrt K) (K-1) ≤ 49/Real.sqrt K := by
  have hKr : (2:ℝ) ≤ K := by exact_mod_cast hK
  have hKp : (0:ℝ) < K := by linarith
  have hy : 0 < Real.sqrt K := Real.sqrt_pos.mpr hKp
  have hy1 : 1 ≤ Real.sqrt K := by
    exact (Real.one_le_sqrt).mpr (by linarith)
  have hcast : ((K-1 : ℕ):ℝ)=(K:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hs := survive_exp (q := 1/Real.sqrt K) ((div_le_one hy).mpr hy1) (K-1)
  rw [hcast] at hs
  have he : -(1/Real.sqrt K*((K:ℝ)-1)) = -(((K:ℝ)-1)/Real.sqrt K) := by ring
  rw [he] at hs
  have hb := (mul_le_mul_of_nonneg_left hs hKp.le).trans (short_exponential_bound hKr)
  have hsum := add_le_add_left hb (1/Real.sqrt K)
  convert hsum using 1 <;> first | rfl | ring

end KServer.RosterLifetimes

end


/-! Literal actual roster lifetime tape, separate from the auxiliary short
roster.  Every construction below is finite at the prescribed horizon. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.ActualRoster
open RosterLifetimes FiniteSurvival Chronological FiniteBallLaw PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

lemma rate_range {K : ℕ} (hK : 1 ≤ K) : 1/(K:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
  have hk : (1:ℝ) ≤ K := by exact_mod_cast hK
  exact ⟨by positivity,(div_le_one (by linarith)).mpr hk⟩

lemma survival_range {K : ℕ} (hK : 1 ≤ K) (a : ℕ) : actualPresence K a ∈ Set.Icc (0:ℝ) 1 := by
  unfold actualPresence
  split_ifs
  · exact ⟨zero_le_one,le_rfl⟩
  · exact survive_range (rate_range hK) _
  · exact ⟨le_rfl,zero_le_one⟩

lemma survival_antitone {K : ℕ} (hK : 1 ≤ K) : Antitone (actualPresence K) := by
  intro a b hab
  by_cases hb : b < K
  · rw [actual_guaranteed hb,actual_guaranteed (lt_of_le_of_lt hab hb)]
  · by_cases hcut : K^2 ≤ b
    · rw [actual_cutoff hcut]
      exact (survival_range hK a).1
    · by_cases ha : a < K
      · rw [actual_guaranteed ha]
        exact (survival_range hK b).2
      · have hac : a < K^2 := lt_of_le_of_lt hab (lt_of_not_ge hcut)
        simp only [actualPresence,ite_eq_right hb,ite_eq_left (lt_of_not_ge hcut),ite_eq_right ha,ite_eq_left hac]
        exact survive_mono (rate_range hK) (by omega)

abbrev Lifetime (K : ℕ) := Fin (K^2)

def lifetimeLaw (K : ℕ) (d : Lifetime K) : ℝ := weight (actualPresence K) d

lemma lifetime_nonneg {K : ℕ} (hK : 1 ≤ K) (d : Lifetime K) : 0 ≤ lifetimeLaw K d :=
  weight_nonneg (survival_antitone hK) d

lemma lifetime_sum {K : ℕ} (hK : 1 ≤ K) : ∑ d : Lifetime K, lifetimeLaw K d=1 := by
  change (∑ d : Fin (K^2), weight (actualPresence K) d)=1
  rw [weight_sum,actual_guaranteed (lt_of_lt_of_le Nat.zero_lt_one hK),actual_cutoff le_rfl]
  norm_num

/-- Certain initial ages are included even on zero-weight tape outcomes; this
makes deterministic coverage a pathwise property, not just an almost-sure one. -/
def alive (K a : ℕ) (d : Lifetime K) : Prop := a<K ∨ a≤(d:ℕ)

lemma alive_young {K a : ℕ} {d : Lifetime K} (h : alive K a d) : a<K^2 := by
  rcases h with h|h
  · have hk : K ≤ K^2 := by nlinarith [Nat.zero_le K]
    exact h.trans_le hk
  · exact h.trans_lt d.isLt

lemma alive_certain {K a : ℕ} (ha : a<K) (d : Lifetime K) : alive K a d := Or.inl ha

lemma alive_probability {K : ℕ} (hK : 1 ≤ K) (a : ℕ) :
    (∑ d : Lifetime K, if alive K a d then lifetimeLaw K d else 0)=actualPresence K a := by
  by_cases ha : a < K
  · simp only [alive,ha,true_or,ite_true,actual_guaranteed ha]
    exact lifetime_sum hK
  · by_cases hc : a ≤ K^2
    · simp only [alive,ha,false_or]
      have hv := probability_living (actualPresence K) (K^2) a hc
      rw [actual_cutoff le_rfl,sub_zero] at hv
      calc (∑ d : Lifetime K, if a≤(d:ℕ) then lifetimeLaw K d else 0)
          = FiniteSurvival.probability (actualPresence K) (fun d : Fin (K^2)=>a≤(d:ℕ)) := by
            unfold FiniteSurvival.probability
            apply sum_congr rfl
            intro d _
            by_cases hd : a≤(d:ℕ) <;> simp [hd,lifetimeLaw]
           _ = actualPresence K a := hv
    · rw [actual_cutoff (le_of_lt (lt_of_not_ge hc))]
      apply sum_eq_zero
      intro d _
      exact ite_eq_right (fun h=>hc (alive_young h).le)

lemma alive_antitone (K : ℕ) (d : Lifetime K) {a b : ℕ} (hab : a≤b) (h : alive K b d) : alive K a d := by
  rcases h with h|h
  · exact Or.inl (lt_of_le_of_lt hab h)
  · exact Or.inr (hab.trans h)

lemma death_probability {K : ℕ} (hK : 1 ≤ K) (a : ℕ) :
    (∑ d : Lifetime K, if alive K a d ∧ ¬alive K (a+1) d then lifetimeLaw K d else 0)=
      actualPresence K a-actualPresence K (a+1) := by
  rw [←alive_probability hK a,←alive_probability hK (a+1),←sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  by_cases hn : alive K (a+1) d
  · have ho := alive_antitone K d (Nat.le_succ _) hn
    simp [hn,ho]
  · simp [hn]

/-- Before the compulsory age, the inverse-tail tape has exactly the source
hazard 1/K once independent trials have begun. -/
lemma ordinary_death_bound {K a : ℕ} (hK : 1 ≤ K) (ha : a+1<K^2) :
    actualPresence K a-actualPresence K (a+1) ≤ (1/(K:ℝ))*actualPresence K a := by
  by_cases hc : a+1<K
  · rw [actual_guaranteed hc,actual_guaranteed (by omega)]
    have hq := (rate_range hK).1
    simpa only [sub_self,mul_one] using hq
  · by_cases hb : a<K
    · have he : a+1=K := by omega
      rw [actual_guaranteed hb]
      simp only [actualPresence,he,lt_self_iff_false,ite_false,show K<K^2 from he ▸ ha,ite_true,
        Nat.sub_self,zero_add,survive,pow_one,mul_one]
      ring_nf
      rfl
    · have hab : a<K^2 := by omega
      have hn : ¬a+1<K := by omega
      simp only [actualPresence,ite_eq_right hb,ite_eq_left hab,ite_eq_right hn,ite_eq_left ha]
      have he : a+1-K+1=(a-K+1)+1 := by omega
      rw [he]
      simp only [survive,pow_succ]
      nlinarith

variable {Y : Type*} [MetricSpace Y] {H K : ℕ}

def present (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (tape : Fin H → Lifetime K) (i : Fin H) : Prop :=
  (i:ℕ)∈I ∧ alive K (age center I (20*r) i) (tape i)

lemma present_young (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (tape : Fin H → Lifetime K) (i : Fin H)
    (hp : present center I r tape i) : (i:ℕ)∈I ∧ age center I (20*r) i<K^2 :=
  ⟨hp.1,alive_young hp.2⟩

lemma young_present (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (tape : Fin H → Lifetime K) (i : Fin H)
    (hi : (i:ℕ)∈I) (ha : age center I (20*r) i<K) : present center I r tape i :=
  ⟨hi,alive_certain ha _⟩

section Radius
variable [Fintype Y]

def covered (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (life : Fin H → Lifetime K)
    (radii : Fin H → Outcome Y r) (x : Y) (i : Fin H) : Prop :=
  present center I r life i ∧ dist (center i) x ≤ radius r (radii i)

def first (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (life : Fin H → Lifetime K)
    (radii : Fin H → Outcome Y r) (x : Y) : Option (Fin H) :=
  let C:=univ.filter (covered center I r life radii x)
  if h:C.Nonempty then some (C.min' h) else none

lemma first_some_iff (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (life : Fin H → Lifetime K)
    (radii : Fin H → Outcome Y r) (x : Y) (i : Fin H) :
    first center I r life radii x=some i ↔
      covered center I r life radii x i ∧ ∀ j < i,¬covered center I r life radii x j := by
  dsimp only [first]
  split_ifs with h
  · constructor
    · intro he
      have hi : (univ.filter (covered center I r life radii x)).min' h=i := Option.some.inj he
      constructor
      · rw [←hi]
        exact (mem_filter.mp (min'_mem _ _)).2
      · intro j hj hc
        have hmin := min'_le (univ.filter (covered center I r life radii x)) j (mem_filter.mpr ⟨mem_univ _,hc⟩)
        rw [hi] at hmin
        exact (not_le_of_gt hj) hmin
    · rintro ⟨hi,hbefore⟩
      congr 1
      apply le_antisymm
      · exact min'_le _ _ (mem_filter.mpr ⟨mem_univ _,hi⟩)
      · by_contra hh
        exact hbefore _ (lt_of_not_ge hh) (mem_filter.mp (min'_mem _ _)).2
  · constructor
    · simp
    · intro hi
      exact False.elim (h ⟨i,mem_filter.mpr ⟨mem_univ _,hi.1⟩⟩)

lemma first_none_iff (center : ℕ → Y) (I : Finset ℕ) (r : ℝ) (life : Fin H → Lifetime K)
    (radii : Fin H → Outcome Y r) (x : Y) :
    first center I r life radii x=none ↔ ∀ i,¬covered center I r life radii x i := by
  simp [first,Finset.not_nonempty_iff_eq_empty,Finset.filter_eq_empty_iff]

/-- Deterministic source coverage on a qualifying insertion step, including
zero-weight lifetime outcomes. -/
lemma qualified_covered (center : ℕ → Y) {r : ℝ} (hr : 0 < r) (hK : 0<K)
    (qualifies : ℕ → Prop) (t : ℕ) (ht : t<H) (hq : qualifies t)
    (life : Fin H → Lifetime K) (radii : Fin H → Outcome Y r) :
    ∃ i, covered center (schedule center r K qualifies (t+1)) r life radii (center t) i := by
  obtain ⟨i,hi,ha,hd⟩ := qualified_coverage center r K qualifies t hK hr.le hq
  have hiH : i < H := (schedule_before center r K qualifies (t+1) i hi).trans_le (by omega)
  refine ⟨⟨i,hiH⟩,young_present _ _ _ _ _ hi ha,?_⟩
  exact hd.trans ((by linarith : r/2 ≤ r).trans (radius_range hr _).1)

/-- Actual fixed-schedule first-hit probability under the complete finite
radius tape, with the independently sampled lifetime tape fixed arbitrarily. -/
theorem first_hit_estimate (center : ℕ → Y) (I : Finset ℕ) {r : ℝ} (hr : 0 < r)
    (hK : 1 ≤ K) (life : Fin H → Lifetime K) (x y : Y) (hxy : dist x y ≤ r) :
    PartitionProbabilities.probability (fun _ : Fin H => law (Y:=Y) (Real.log (1+(K:ℝ)^2)) r)
      (firstSeparation (fun j d => present center I r life j ∧ hit r (center j) x y d)
        (fun j d => present center I r life j ∧ separates r (center j) x y d)) ≤
      2*Real.log (1+(K:ℝ)^2)*dist x y/r :=
  SparseFirstHit.chronological_roster_bound hK hr center I _ (present_young center I r life) x y hxy

end Radius
end KServer.ActualRoster

end

end OAI
