import Mathlib
import OAI.Combinatorics.KServer.Rosters

namespace OAI

/- Analytic insertion gain for the second compact pilot under the profile hypotheses. -/


noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.Pilot
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [Fintype Y] [MetricSpace Y] [DecidableEq Y]

omit [DecidableEq Y] in
lemma residual_bounds {T : Template} {r : ℝ} {z : Y → ℝ}
    (hz : Feasible T r z) (p : Y) :
    1-∑ s,z s*b T (dist s p/r) ∈ Set.Icc 0 1 := by
  refine ⟨sub_nonneg.mpr (sum_b_le_one hz p),?_⟩
  have hh := sum_nonneg (s := (univ : Finset Y))
    (fun s _ => mul_nonneg (hz.1 s) (b_nonneg T (dist s p/r)))
  linarith

omit [DecidableEq Y] in
lemma profile_difference (T : Template) (r : ℝ) (g₀ g₁ z : Y → ℝ) (p : Y) :
    integrand T r g₀ z p-integrand T r g₁ z p =
      (g₀ p-g₁ p)*(1-∑ s,z s*b T (dist s p/r))+
        256*∑ s,z s*(g₀ s-g₁ s)*a T (dist s p/r) := by
  have he : (∑ s,z s*(1+g₀ s)*a T (dist s p/r))-
      (∑ s,z s*(1+g₁ s)*a T (dist s p/r)) =
      ∑ s,z s*(g₀ s-g₁ s)*a T (dist s p/r) := by
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intros
    ring
  unfold integrand
  linear_combination 256*he

omit [DecidableEq Y] in
/-- A narrow residual has deficit at most one half unless a nearby pilot
site has weight at least one half. Separation, not a new assumption about
sparsity, proves that at most one positive bump contributes. -/
lemma residual_half {T : Template} {r γ : ℝ} {z : Y → ℝ} {x p : Y}
    (hr : 0<r) (hγ : γ<T.σ) (hz : Feasible T r z)
    (hn : ∀ s,dist s x<3*T.σ*r → z s<1/2)
    (hp : dist x p≤γ*r) : 1/2 ≤ 1-∑ s,z s*b T (dist s p/r) := by
  have hterm : ∀ s,0≤z s*b T (dist s p/r) :=
    fun s => mul_nonneg (hz.1 s) (b_nonneg T _)
  have hsingle : ∀ s,0<z s*b T (dist s p/r) → z s*b T (dist s p/r)≤1/2 := by
    intro s hs
    have hzpos : 0<z s := (mul_pos_iff.mp hs).resolve_right (by intro h; linarith [hz.1 s]) |>.1
    have hbpos : 0<b T (dist s p/r) :=
      (mul_pos_iff.mp hs).resolve_right (by intro h; linarith [hz.1 s]) |>.2
    have hd : dist s p<2*T.σ*r := (div_lt_iff₀ hr).mp (b_pos_iff.mp hbpos)
    have hnear : dist s x<3*T.σ*r := by
      have ht := dist_triangle s p x
      rw [dist_comm p x] at ht
      have hm := mul_lt_mul_of_pos_right hγ hr
      linarith
    exact (mul_le_of_le_one_right (hz.1 s) (b_le_one T _)).trans (hn s hnear).le
  have huniq : ∀ s t,0<z s*b T (dist s p/r) → 0<z t*b T (dist t p/r) → s=t := by
    intro s t hs ht
    have hs' := (mul_pos_iff.mp hs).resolve_right (by intro h; linarith [hz.1 s])
    have ht' := (mul_pos_iff.mp ht).resolve_right (by intro h; linarith [hz.1 t])
    exact positive_b_support_disjoint hr hz hs'.1 ht'.1 hs'.2 ht'.2
  have hh := sum_unique_le (f := fun s => z s*b T (dist s p/r))
    (q := (1/2:ℝ)) (by norm_num) hterm
      (fun s => by by_cases hs : 0<z s*b T (dist s p/r); exact hsingle s hs
                   exact (le_of_not_gt hs).trans (by norm_num)) huniq
  linarith

omit [DecidableEq Y] in
/-- Correcting each coefficient by epsilon uses the pilot capacity once,
not the number of sites. -/
lemma surcharge_error {T : Template} {r ε : ℝ} {z d : Y → ℝ} (hz : Feasible T r z)
    (hε : 0≤ε) (hd : ∀ s,-ε≤d s) (p : Y) :
    -ε ≤ ∑ s,z s*d s*a T (dist s p/r) := by
  have hb := sum_le_sum (s := (univ : Finset Y)) fun s _ =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hd s) (hz.1 s)) (a_nonneg T (dist s p/r))
  have he : (∑ s,z s*(-ε)*a T (dist s p/r))=
      -ε*∑ s,z s*a T (dist s p/r) := by
    rw [mul_sum]
    apply sum_congr rfl
    intros
    ring
  rw [he] at hb
  have hc := mul_le_mul_of_nonneg_left (sum_a_le_one hz p) hε
  linarith

omit [DecidableEq Y] in
lemma surcharge_gain {T : Template} {r ε : ℝ} {z d : Y → ℝ} (hz : Feasible T r z)
    (hε : 0≤ε) (hd : ∀ i,-ε≤d i) (s p : Y) (hs : d s=1) (hzs : 1/2≤z s)
    (ha : a T (dist s p/r)=1) :
    1/2-ε ≤ ∑ i,z i*d i*a T (dist i p/r) := by
  have hn i : 0≤z i*(d i+ε)*a T (dist i p/r) :=
    mul_nonneg (mul_nonneg (hz.1 i) (by linarith [hd i])) (a_nonneg T _)
  have hb := single_le_sum (s := (univ : Finset Y)) (fun i _ => hn i) (mem_univ s)
  have he : (∑ i,z i*(d i+ε)*a T (dist i p/r))=
      (∑ i,z i*d i*a T (dist i p/r))+ε*∑ i,z i*a T (dist i p/r) := by
    rw [mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intros
    ring
  rw [he,hs,ha,mul_one] at hb
  have hc := mul_le_mul_of_nonneg_left (sum_a_le_one hz p) hε
  have hzε : 1/2≤z s*(1+ε) := by nlinarith [hz.1 s]
  linarith

omit [MetricSpace Y] in
lemma indicator_sum (μ : Y → ℝ) (A : Finset Y) :
    (∑ p,μ p*(if p∈A then (1:ℝ) else 0))=mass μ A := by
  simp only [mul_ite,mul_one,mul_zero,←sum_filter,filter_mem_eq_inter,Finset.univ_inter,mass]

/-- Common signed error estimate, including exact support. -/
lemma profile_error {T : Template} {r ε : ℝ} {z g₀ g₁ : Y → ℝ}
    (hz : Feasible T r z) (hε : 0≤ε) (hd : ∀ i,-ε≤g₀ i-g₁ i) (W : Finset Y)
    (hres : ∀ p,p∉W → 0≤g₀ p-g₁ p)
    (hsur : ∀ p,p∉W → ∀ i,0≤z i*(g₀ i-g₁ i)*a T (dist i p/r)) (p : Y) :
    -257*ε*(if p∈W then (1:ℝ) else 0) ≤ integrand T r g₀ z p-integrand T r g₁ z p := by
  rw [profile_difference]
  have hR := residual_bounds hz p
  by_cases hp : p∈W
  · rw [ite_eq_left hp,mul_one]
    have hm := mul_le_mul_of_nonneg_right (hd p) hR.1
    have he := mul_le_mul_of_nonneg_left hR.2 hε
    have hs := surcharge_error hz hε hd p
    nlinarith
  · rw [ite_eq_right hp,mul_zero]
    exact add_nonneg (mul_nonneg (hres p hp) hR.1)
      (mul_nonneg (by norm_num) (sum_nonneg (fun i _ => hsur p hp i)))

/-- A residual gain is added to the common signed error, pointwise. -/
lemma profile_residual_gain {T : Template} {r ε : ℝ} {z g₀ g₁ : Y → ℝ}
    (hz : Feasible T r z) (hε : 0≤ε) (hd : ∀ i,-ε≤g₀ i-g₁ i) (W A : Finset Y)
    (hres : ∀ p,p∉W → 0≤g₀ p-g₁ p)
    (hsur : ∀ p,p∉W → ∀ i,0≤z i*(g₀ i-g₁ i)*a T (dist i p/r))
    (hgain : ∀ p∈A,g₀ p-g₁ p=1 ∧ 1/2≤1-∑ s,z s*b T (dist s p/r)) (p : Y) :
    (1/2:ℝ)*(if p∈A then 1 else 0)-257*ε*(if p∈W then (1:ℝ) else 0) ≤
      integrand T r g₀ z p-integrand T r g₁ z p := by
  by_cases hp : p∈A
  · have hg := hgain p hp
    rw [ite_eq_left hp,mul_one,profile_difference,hg.1,one_mul]
    by_cases hw : p∈W
    · rw [ite_eq_left hw,mul_one]
      have hs := surcharge_error hz hε hd p
      linarith
    · rw [ite_eq_right hw,mul_zero,sub_zero]
      have hs := sum_nonneg (s := (univ : Finset Y)) (fun i _ => hsur p hw i)
      linarith [hg.2]
  · rw [ite_eq_right hp,mul_zero,zero_sub]
    convert profile_error hz hε hd W hres hsur p using 1; (first | rfl | ring)

/-- A known near site creates a surcharge gain, pointwise. -/
lemma profile_surcharge_gain {T : Template} {r ε : ℝ} {z g₀ g₁ : Y → ℝ}
    (hz : Feasible T r z) (hε : 0≤ε) (hd : ∀ i,-ε≤g₀ i-g₁ i) (W A : Finset Y)
    (hres : ∀ p,p∉W → 0≤g₀ p-g₁ p)
    (hsur : ∀ p,p∉W → ∀ i,0≤z i*(g₀ i-g₁ i)*a T (dist i p/r))
    (s : Y) (hs : g₀ s-g₁ s=1) (hzs : 1/2≤z s)
    (ha : ∀ p∈A,a T (dist s p/r)=1) (p : Y) :
    128*(if p∈A then (1:ℝ) else 0)-257*ε*(if p∈W then (1:ℝ) else 0) ≤
      integrand T r g₀ z p-integrand T r g₁ z p := by
  by_cases hp : p∈A
  · have hR := residual_bounds hz p
    rw [ite_eq_left hp,mul_one,profile_difference]
    by_cases hw : p∈W
    · rw [ite_eq_left hw,mul_one]
      have hsg := surcharge_gain hz hε hd s p hs hzs (ha p hp)
      have hm := mul_le_mul_of_nonneg_right (hd p) hR.1
      have he := mul_le_mul_of_nonneg_left hR.2 hε
      nlinarith
    · rw [ite_eq_right hw,mul_zero,sub_zero]
      have hsg := single_le_sum (s := (univ : Finset Y))
        (fun i _ => hsur p hw i) (mem_univ s)
      rw [hs,ha p hp,mul_one,mul_one] at hsg
      have hrn := mul_nonneg (hres p hw) hR.1
      linarith
  · rw [ite_eq_right hp,mul_zero,zero_sub]
    convert profile_error hz hε hd W hres hsur p using 1; (first | rfl | ring)

/-- Integrating a pointwise pilot edit estimate and testing the literal old
minimizer proves a minimum decrease; no decrease assumption is needed. -/
lemma potential_profile_gain {T : Template} {r c e : ℝ} {μ g₀ g₁ : Y → ℝ}
    (hr : 0≤r) (hμ : ∀ p,0≤μ p) (A W : Finset Y)
    (hpoint : ∀ p,c*(if p∈A then (1:ℝ) else 0)-e*(if p∈W then (1:ℝ) else 0) ≤
      integrand T r g₀ (minimizer T r μ g₀) p-
        integrand T r g₁ (minimizer T r μ g₀) p) :
    r*(c*mass μ A-e*mass μ W) ≤ potential T r μ g₀-potential T r μ g₁ := by
  have hb := sum_le_sum (s := (univ : Finset Y)) fun p _ =>
    mul_le_mul_of_nonneg_left (hpoint p) (hμ p)
  have he : (∑ p,μ p*(c*(if p∈A then (1:ℝ) else 0)-e*(if p∈W then (1:ℝ) else 0)))=
      c*mass μ A-e*mass μ W := by
    simp only [mul_sub,sum_sub_distrib,mul_left_comm (μ _) c,mul_left_comm (μ _) e,
      ←mul_sum,indicator_sum]
  rw [he] at hb
  have hm := mul_le_mul_of_nonneg_left hb hr
  have he' : r*∑ p,μ p*(integrand T r g₀ (minimizer T r μ g₀) p-
      integrand T r g₁ (minimizer T r μ g₀) p) =
      potential T r μ g₀-objective T r μ g₁ (minimizer T r μ g₀) := by
    simp only [mul_sub,sum_sub_distrib,mul_sub,potential,objective]
  rw [he'] at hm
  exact hm.trans (sub_le_sub_left (potential_le (minimizer_spec T r μ g₀).1) _)

omit [DecidableEq Y] in
/-- A coefficient lower bound using the actual bump supports on any two
finite regions. Used for the heavy annular version of the tier edit. -/
lemma coefficient_lower {T : Template} {r : ℝ} {μ g : Y → ℝ} (s : Y)
    (hμ : ∀ p,0≤μ p) (hg : ∀ p,g p∈Set.Icc 0 1) (A B : Finset Y)
    (ha : ∀ p∈A,a T (dist s p/r)=1)
    (hb : ∀ p,b T (dist s p/r)≠0 → p∈B) :
    256*mass μ A-2*mass μ B ≤ coefficient T r μ g s := by
  have hapos : 256*mass μ A ≤ ∑ p,μ p*(256*(1+g s)*a T (dist s p/r)) := by
    calc _ ≤ ∑ p∈A,μ p*(256*(1+g s)*a T (dist s p/r)) := by
           unfold mass
           rw [mul_sum]
           apply sum_le_sum
           intro p hp
           rw [ha p hp,mul_one]
           nlinarith [mul_nonneg (hμ p) (hg s).1]
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun p _ _ =>
           mul_nonneg (hμ p) (mul_nonneg (by linarith [(hg s).1]) (a_nonneg _ _)))
  have hbneg : (∑ p,μ p*((1+g p)*b T (dist s p/r))) ≤ 2*mass μ B := by
    calc _ = ∑ p∈B,μ p*((1+g p)*b T (dist s p/r)) := by
           apply (sum_subset (subset_univ _) ?_).symm
           intro p _ hnot
           have hz : b T (dist s p/r)=0 := by by_contra hn; exact hnot (hb p hn)
           simp [hz]
         _ ≤ _ := by
           unfold mass
           rw [mul_sum]
           apply sum_le_sum
           intro p _
           have hh : (1+g p)*b T (dist s p/r)≤2 := by
             nlinarith [mul_nonneg (hg p).1 (sub_nonneg.mpr (b_le_one T (dist s p/r))),
               b_nonneg T (dist s p/r),(hg p).1,(hg p).2,b_le_one T (dist s p/r)]
           nlinarith [mul_le_mul_of_nonneg_left hh (hμ p)]
  unfold coefficient
  simp only [mul_sub,sum_sub_distrib]
  linarith

lemma a_eq_one {T : Template} {v : ℝ} (hv : T.σ≤v) (hR : v≤T.R) : a T v=1 := by
  rw [a,ite_eq_left hR]
  apply min_eq_right
  apply (le_div_iff₀ (sq_pos_of_pos T.σ_pos)).mpr
  nlinarith [T.σ_pos]

end KServer.Pilot

end


noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.Pilot
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [Fintype Y] [MetricSpace Y] [DecidableEq Y]

omit [DecidableEq Y] in
lemma tier_increasing_site_zero {T : Template} {r γ δ : ℝ} {μ g z : Y → ℝ} {x s : Y}
    (hr : 0<r) (hσ : T.σ≤1/1000) (hγ : γ≤1/100) (hδ : δ≤1)
    (hμ : ∀ p,0≤μ p) (hg : ∀ p,g p∈Set.Icc 0 1)
    (hz : Feasible T r z) (hmin : IsMinOn (objective T r μ g) {w | Feasible T r w} z)
    (hM : 0 < mass μ (ball x (γ*r)))
    (hconc : mass μ (ball x (51200*r))≤(1+δ)*mass μ (ball x (γ*r)))
    (hslo : r/8<dist s x) (hshi : dist s x≤21*r) : z s=0 := by
  apply minimizer_zero_of_coefficient_pos hr hz hmin
  have ha : ∀ p∈ball x (γ*r),a T (dist s p/r)=1 := by
    intro p hp
    have hp' := (mem_filter.mp hp).2
    apply a_eq_one
    · apply (le_div_iff₀ hr).mpr
      have ht := dist_triangle s p x
      rw [dist_comm p x] at ht
      have hg' := mul_le_mul_of_nonneg_right hγ hr.le
      have hs' := mul_le_mul_of_nonneg_right hσ hr.le
      linarith
    · apply (div_le_iff₀ hr).mpr
      have ht := dist_triangle s x p
      have hg' := mul_le_mul_of_nonneg_right hγ hr.le
      have hR' := mul_le_mul_of_nonneg_right T.R_ge hr.le
      linarith
  have hb : ∀ p,b T (dist s p/r)≠0 → p∈ball x (51200*r) := by
    intro p hp
    have hbpos : 0<b T (dist s p/r) := lt_of_le_of_ne (b_nonneg _ _) (Ne.symm hp)
    have hd := (div_lt_iff₀ hr).mp (b_pos_iff.mp hbpos)
    have ht := dist_triangle x s p
    rw [dist_comm x s] at ht
    have hs' := mul_le_mul_of_nonneg_right hσ hr.le
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    linarith
  have hc := coefficient_lower s hμ hg (ball x (γ*r)) (ball x (51200*r)) ha hb
  have hδ' := mul_le_mul_of_nonneg_right hδ hM.le
  linarith

lemma tier_near_bump {T : Template} {r γ : ℝ} {x s p : Y}
    (hr : 0<r) (hσ : T.σ≤1/1000) (hR : 51201≤T.R) (hγ : 10*T.σ<γ)
    (hs : dist s x<3*T.σ*r)
    (hp : p∈ball x (51200*r) \ ball x (γ*r)) : a T (dist s p/r)=1 := by
  have hpout := (mem_filter.mp (mem_sdiff.mp hp).1).2
  have hpin : γ*r<dist x p := by
    have hnot := (mem_sdiff.mp hp).2
    by_contra hn
    exact hnot (mem_filter.mpr ⟨mem_univ _,le_of_not_gt hn⟩)
  apply a_eq_one
  · apply (le_div_iff₀ hr).mpr
    have ht := dist_triangle x s p
    rw [dist_comm x s] at ht
    have hg' := mul_lt_mul_of_pos_right hγ hr
    nlinarith [mul_pos T.σ_pos hr]
  · apply (div_le_iff₀ hr).mpr
    have ht := dist_triangle s x p
    have hσ' := mul_le_mul_of_nonneg_right hσ hr.le
    have hR' := mul_le_mul_of_nonneg_right hR hr.le
    linarith

omit [DecidableEq Y] in
lemma tier_outer_surcharge_nonneg {T : Template} {r : ℝ} {z d : Y → ℝ} {x p : Y}
    (hr : 0<r) (hz : Feasible T r z)
    (hsupp : ∀ i,d i<0 → dist x i≤21*r)
    (hp : p∉ball x (100*T.R*r)) (i : Y) : 0≤z i*d i*a T (dist i p/r) := by
  by_cases hd : 0≤d i
  · exact mul_nonneg (mul_nonneg (hz.1 i) hd) (a_nonneg T _)
  · have hi := hsupp i (lt_of_not_ge hd)
    have ha : a T (dist i p/r)=0 := by
      apply a_eq_zero
      apply (le_div_iff₀ hr).mpr
      have hp' : 100*T.R*r<dist x p := by
        by_contra hn
        exact hp (mem_filter.mpr ⟨mem_univ _,le_of_not_gt hn⟩)
      have ht := dist_triangle x i p
      have hR := mul_le_mul_of_nonneg_right T.R_ge hr.le
      linarith
    simp [ha]

/-- The finite region whose mass is charged by one real tier insertion. -/
def tierRegion (T : Template) (r γ δ : ℝ) (μ : Y → ℝ) (x : Y) : Finset Y :=
  if mass μ (ball x (51200*r))≤(1+δ)*mass μ (ball x (γ*r)) then
    ball x (51200*r) \ ball x (γ*r)
  else ball x (100*T.R*r)

lemma tierRegion_subset (T : Template) {r γ δ : ℝ} (hr : 0≤r)
    (μ : Y → ℝ) (x : Y) (hR : 51201≤T.R) :
    tierRegion T r γ δ μ x ⊆ ball x (100*T.R*r) := by
  unfold tierRegion
  split_ifs
  · intro p hp
    have hp' := (mem_filter.mp (mem_sdiff.mp hp).1).2
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    have hm := mul_le_mul_of_nonneg_right hR hr
    nlinarith
  · exact subset_refl _

/-- Geometry discharges the signed-error support with the annular heavy
region, rather than paying the possibly large inner heavy mass. -/
lemma tier_error_support {T : Template} {r γ δ : ℝ} {μ g₀ g₁ z : Y → ℝ} {x : Y}
    (hr : 0<r) (hσ : T.σ≤1/1000) (hγ : γ≤1/100) (hδ : δ≤1)
    (hμ : ∀ p,0≤μ p) (hg : ∀ p,g₀ p∈Set.Icc 0 1)
    (hz : Feasible T r z) (hmin : IsMinOn (objective T r μ g₀) {w | Feasible T r w} z)
    (hM : 0 < mass μ (ball x (γ*r)))
    (hdrop : ∀ p,dist x p≤r/8 → g₀ p-g₁ p=1)
    (hsupp : ∀ p,g₀ p-g₁ p<0 → dist x p≤21*r) :
    (∀ p,p∉tierRegion T r γ δ μ x → 0≤g₀ p-g₁ p) ∧
    (∀ p,p∉tierRegion T r γ δ μ x → ∀ i,0≤z i*(g₀ i-g₁ i)*a T (dist i p/r)) := by
  have hlow (i : Y) (hi : g₀ i-g₁ i<0) : r/8<dist x i := by
    by_contra hn
    rw [hdrop i (le_of_not_gt hn)] at hi
    norm_num at hi
  by_cases hheavy : mass μ (ball x (51200*r))≤(1+δ)*mass μ (ball x (γ*r))
  · have hreg : tierRegion T r γ δ μ x=ball x (51200*r) \ ball x (γ*r) :=
      ite_eq_left hheavy
    constructor
    · intro p hp
      by_contra hn
      have hd := lt_of_not_ge hn
      apply hp
      rw [hreg]
      apply mem_sdiff.mpr
      constructor
      · apply mem_filter.mpr ⟨mem_univ _,?_⟩
        linarith [hsupp p hd]
      · intro hh
        have hp' := (mem_filter.mp hh).2
        have hγ' := mul_le_mul_of_nonneg_right hγ hr.le
        linarith [hlow p hd]
    · intro p _ i
      by_cases hi : 0≤g₀ i-g₁ i
      · exact mul_nonneg (mul_nonneg (hz.1 i) hi) (a_nonneg T _)
      · have he : z i=0 := tier_increasing_site_zero hr hσ hγ hδ hμ hg hz hmin hM hheavy
          (by simpa only [dist_comm i x] using hlow i (lt_of_not_ge hi))
          (by simpa only [dist_comm i x] using hsupp i (lt_of_not_ge hi))
        simp [he]
  · have hreg : tierRegion T r γ δ μ x=ball x (100*T.R*r) := ite_eq_right hheavy
    constructor
    · intro p hp
      by_contra hn
      apply hp
      rw [hreg]
      apply mem_filter.mpr ⟨mem_univ _,?_⟩
      have ht := hsupp p (lt_of_not_ge hn)
      have hR := mul_le_mul_of_nonneg_right T.R_ge hr.le
      linarith
    · intro p hp i
      rw [hreg] at hp
      exact tier_outer_surcharge_nonneg hr hz hsupp hp i

/-- Tier-pilot drop, including the heavy annular refinement. The
profile hypotheses describe the actual short-roster update; no pilot drop,
site existence, or coefficient-vanishing statement is assumed. -/
theorem tier_pilot_drop {T : Template} {r γH γL δ h ε : ℝ} {μ g₀ g₁ : Y → ℝ} {x : Y}
    (hr : 0<r) (hσ : T.σ≤1/1000) (hR : 51201≤T.R)
    (hγH : γH≤1/100) (hσH : 10*T.σ<γH) (hγL : γL<T.σ)
    (hδ0 : 0≤δ) (hδ : δ≤1/256) (hh : 0≤h) (hε : 0≤ε)
    (hμ : ∀ p,0≤μ p) (hg : ∀ p,g₀ p∈Set.Icc 0 1)
    (hM : 0 < mass μ (ball x (γL*r)))
    (hqual : mass μ (ball x (100*T.R*r))≤Real.exp h*mass μ (ball x (γL*r)))
    (hd : ∀ p,-ε≤g₀ p-g₁ p)
    (hdrop : ∀ p,dist x p≤r/8 → g₀ p-g₁ p=1)
    (hsupp : ∀ p,g₀ p-g₁ p<0 → dist x p≤21*r) :
    r*mass μ (tierRegion T r γH δ μ x)*(128*δ*Real.exp (-h)-257*ε) ≤
      potential T r μ g₀-potential T r μ g₁ := by
  let z := minimizer T r μ g₀
  let W := tierRegion T r γH δ μ x
  let A := ball x (51200*r) \ ball x (γH*r)
  have hz : Feasible T r z := (minimizer_spec T r μ g₀).1
  have hmin := (minimizer_spec T r μ g₀).2
  have hLH : ball x (γL*r) ⊆ ball x (γH*r) := by
    apply ball_mono
    have hLH : γL≤γH := by linarith [T.σ_pos]
    exact mul_le_mul_of_nonneg_right hLH hr.le
  have hBH : ball x (γH*r) ⊆ ball x (51200*r) := by
    apply ball_mono
    exact mul_le_mul_of_nonneg_right (by linarith : γH≤51200) hr.le
  have hMH : 0 < mass μ (ball x (γH*r)) := hM.trans_le (mass_mono hμ hLH)
  have hsupport := tier_error_support hr hσ hγH (by linarith : δ≤1) hμ hg hz hmin hMH hdrop hsupp
  have hW0 : 0≤ mass μ W := mass_nonneg hμ W
  have hWI : Real.exp (-h)*mass μ W≤ mass μ (ball x (γL*r)) := by
    have he := mul_le_mul_of_nonneg_left
      ((mass_mono hμ (tierRegion_subset T (γ := γH) (δ := δ) hr.le μ x hR)).trans hqual) (Real.exp_nonneg (-h))
    have heq : Real.exp (-h)*(Real.exp h*mass μ (ball x (γL*r)))=mass μ (ball x (γL*r)) := by
      rw [←mul_assoc,←Real.exp_add]
      simp
    rw [heq] at he
    exact he
  by_cases hn : ∃ s,dist s x<3*T.σ*r ∧ 1/2≤z s
  · obtain ⟨s,hs,hsz⟩ := hn
    have hsdrop : g₀ s-g₁ s=1 := by
      apply hdrop
      rw [dist_comm x s]
      have hm := mul_le_mul_of_nonneg_right hσ hr.le
      linarith
    have hgain := potential_profile_gain hr.le hμ A W
      (profile_surcharge_gain hz hε hd W A hsupport.1 hsupport.2 s hsdrop hsz
        (fun p hp => tier_near_bump hr hσ hR hσH hs hp))
    have hmass : δ*Real.exp (-h)*mass μ W≤ mass μ A := by
      by_cases hheavy : mass μ (ball x (51200*r))≤(1+δ)*mass μ (ball x (γH*r))
      · have heq : W=A := ite_eq_left hheavy
        rw [heq]
        have he : Real.exp (-h)≤1 := by
          rw [Real.exp_le_one_iff]
          linarith
        have hδe : δ*Real.exp (-h)≤1 :=
          (mul_le_mul_of_nonneg_left he hδ0).trans (by linarith)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hδe (mass_nonneg hμ A)
      · have heq := sum_sdiff (f := μ) hBH
        change mass μ A+mass μ (ball x (γH*r))=mass μ (ball x (51200*r)) at heq
        have hMI := mul_le_mul_of_nonneg_left (mass_mono hμ hLH) hδ0
        have hWI' := mul_le_mul_of_nonneg_left hWI hδ0
        have hh' := lt_of_not_ge hheavy
        nlinarith only [heq,hMI,hWI',hh']
    have hm : 128*δ*Real.exp (-h)*mass μ W≤128*mass μ A := by nlinarith only [hmass]
    have hfinal := (mul_le_mul_of_nonneg_left (sub_le_sub_right hm (257*ε*mass μ W)) hr.le).trans hgain
    convert hfinal using 1; (first | rfl | ring)
  · have hn' : ∀ s,dist s x<3*T.σ*r → z s<1/2 := by
      intro s hs
      by_contra hh
      exact hn ⟨s,hs,le_of_not_gt hh⟩
    have hprofile : ∀ p∈ball x (γL*r),g₀ p-g₁ p=1 ∧ 1/2≤1-∑ s,z s*b T (dist s p/r) := by
      intro p hp
      have hp' := (mem_filter.mp hp).2
      constructor
      · apply hdrop
        have hγ' := mul_lt_mul_of_pos_right hγL hr
        have hσ' := mul_le_mul_of_nonneg_right hσ hr.le
        linarith
      · exact residual_half hr hγL hz hn' hp'
    have hgain := potential_profile_gain hr.le hμ (ball x (γL*r)) W
      (profile_residual_gain hz hε hd W (ball x (γL*r)) hsupport.1 hsupport.2 hprofile)
    have hmass : 128*δ*Real.exp (-h)*mass μ W≤(1/2)*mass μ (ball x (γL*r)) := by
      have he := mul_le_mul_of_nonneg_left hWI (show 0≤128*δ by positivity)
      have hc : 128*δ≤1/2 := by linarith
      have hc' := mul_le_mul_of_nonneg_right hc hM.le
      nlinarith only [he,hc']
    have hfinal := (mul_le_mul_of_nonneg_left (sub_le_sub_right hmass (257*ε*mass μ W)) hr.le).trans hgain
    convert hfinal using 1; (first | rfl | ring)

end KServer.Pilot

end


/-! The actual adapted chronological tier process and its all-step compact
pilot payment. No conditional drift or unconstructed roster is postulated. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.TierProcess
open FiniteExperiment RankTracking PosteriorRanks Pilot Chronological
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y] [DecidableEq Y]
variable {k H : ℕ} [NeZero k]

def request (s : Configuration k Y) (σ : Fin H → Y) (t : ℕ) : Y :=
  if ht : t<H then σ ⟨t,ht⟩ else s 0

omit [MetricSpace Y] [Fintype Y] [DecidableEq Y] in
lemma request_fin (s : Configuration k Y) (σ : Fin H → Y) (t : Fin H) :
    request s σ t=σ t := by simp [request,t.isLt]

omit [MetricSpace Y] [DecidableEq Y] in
lemma request_adapted (s : Configuration k Y) {t i : ℕ} (hi : i<t)
    (σ ρ : Fin H → Y) (hh : requestHistory t σ=requestHistory t ρ) :
    request s σ i=request s ρ i := by
  unfold request
  split_ifs with hH
  · have he:=congrFun ((requestHistory_eq_iff _ _ _).mp hh) ⟨i,hH⟩
    simpa [requestPrefix,hi] using he
  · rfl

def qualifies (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (σ : Fin H → Y) (t : ℕ) : Prop :=
  t<H ∧ mass (mu s law (t+1) σ) (ball (request s σ t) (100*T.R*r))≤
    Real.exp h*mass (mu s law (t+1) σ) (ball (request s σ t) (γ*r))

def roster (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K : ℕ) (σ : Fin H → Y) (t : ℕ) : Finset ℕ :=
  schedule (request s σ) r K (qualifies s law T r γ h σ) t

omit [DecidableEq Y] in
lemma roster_succ (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K : ℕ) (σ : Fin H → Y) (t : ℕ) :
    roster s law T r γ h K σ (t+1)=
      if insertTest (request s σ) (roster s law T r γ h K σ t) r K t (qualifies s law T r γ h σ t)
      then insert t (roster s law T r γ h K σ t) else roster s law T r γ h K σ t := rfl

omit [DecidableEq Y] in
lemma roster_before (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K : ℕ) (σ : Fin H → Y) (t : ℕ) :
    ∀ i∈roster s law T r γ h K σ t,i<t :=
  schedule_before _ _ _ _ _

omit [DecidableEq Y] in
lemma roster_adapted (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K : ℕ) (t : ℕ) :
    ∀ σ ρ,requestHistory t σ=requestHistory t ρ →
      roster s law T r γ h K σ t=roster s law T r γ h K ρ t := by
  induction t with
  | zero => intros; rfl
  | succ t ih =>
    intro σ ρ hh
    have hc:=ih σ ρ (requestHistory_refines t σ ρ hh)
    have hreq : ∀ i,i<t+1 → request s σ i=request s ρ i := fun i hi=>request_adapted s hi σ ρ hh
    have hq : qualifies s law T r γ h σ t ↔ qualifies s law T r γ h ρ t := by
      have hμ : mu s law (t+1) σ=mu s law (t+1) ρ := funext (fun y=>mu_adapted s law (t+1) y σ ρ hh)
      simp only [qualifies,hμ,hreq t (by omega)]
    have ha (i : ℕ) (hi : i∈roster s law T r γ h K σ t) :
        age (request s σ) (roster s law T r γ h K σ t) (20*r) i=
        age (request s ρ) (roster s law T r γ h K σ t) (20*r) i :=
      ShortRoster.age_congr (hreq i (by have hh:=roster_before s law T r γ h K σ t i hi; omega))
        (fun j hj=>hreq j (by have hh:=roster_before s law T r γ h K σ t j hj; omega))
    have ht : insertTest (request s σ) (roster s law T r γ h K σ t) r K t (qualifies s law T r γ h σ t) ↔
        insertTest (request s ρ) (roster s law T r γ h K ρ t) r K t (qualifies s law T r γ h ρ t) := by
      unfold insertTest
      rw [←hc,hq]
      refine and_congr Iff.rfl (not_congr ?_)
      apply exists_congr
      intro i
      apply and_congr_right
      intro hi
      rw [ha i hi,hreq i (by have hh:=roster_before s law T r γ h K σ t i hi; omega),hreq t (by omega)]
    rw [roster_succ,roster_succ,ht,hc]

def profile (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K : ℕ) (σ : Fin H → Y) (t : ℕ) (p : Y) : ℝ :=
  ShortRoster.profile (H := H) (request s σ) r K (roster s law T r γ h K σ t) p

omit [DecidableEq Y] in
lemma profile_adapted (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γ h : ℝ) (K t : ℕ) (p : Y) :
    Adapted (requestHistory t) (fun σ=>profile s law T r γ h K σ t p) := by
  intro σ ρ hh
  change ShortRoster.profile (H := H) (request s σ) r K (roster s law T r γ h K σ t) p=
    ShortRoster.profile (H := H) (request s ρ) r K (roster s law T r γ h K ρ t) p
  rw [←roster_adapted s law T r γ h K t σ ρ hh]
  exact ShortRoster.profile_congr (fun j hj=>request_adapted s (roster_before s law T r γ h K σ t j hj) σ ρ hh) r K p

/-- The genuine insertion mass W of the manuscript, zero on noninsertions. -/
def charge (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) (r γH γL δ h : ℝ) (K : ℕ) (t : Fin H) (σ : Fin H → Y) : ℝ :=
  if insertTest (request s σ) (roster s law T r γL h K σ t) r K t
    (qualifies s law T r γL h σ t)
  then r*mass (mu s law (t.val+1) σ) (tierRegion T r γH δ (mu s law (t.val+1) σ) (σ t)) else 0

lemma charge_nonneg (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    (T : Template) {r : ℝ} (hr : 0≤r) (γH γL δ h : ℝ) (K : ℕ) (t : Fin H) (σ : Fin H → Y) :
    0≤charge s law T r γH γL δ h K t σ := by
  unfold charge
  split_ifs
  · exact mul_nonneg hr (mass_nonneg (mu_nonneg s law (t.val+1) σ) _)
  · rfl

lemma charge_le_drop (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {T : Template} {r γH γL δ h : ℝ} {K : ℕ}
    (hr : 0<r) (hK : 2≤K) (hσ : T.σ≤1/1000) (hR : 51201≤T.R)
    (hγH : γH≤1/100) (hσH : 10*T.σ<γH) (hγL0 : 0≤γL) (hγL : γL<T.σ)
    (hδ0 : 0≤δ) (hδ : δ≤1/256) (hh : 0≤h) (t : Fin H) (σ : Fin H → Y) (hs : 0<law.val σ) :
    charge s law T r γH γL δ h K t σ*(128*δ*Real.exp (-h)-257*(49/Real.sqrt K)) ≤
      potential T r (mu s law (t.val+1) σ) (profile s law T r γL h K σ t)-
      potential T r (mu s law (t.val+1) σ) (profile s law T r γL h K σ (t.val+1)) := by
  let S:=roster s law T r γL h K σ t
  have hbefore : ∀ i∈S,i<(t:ℕ) := roster_before s law T r γL h K σ t
  unfold charge
  split_ifs with ht
  · have hnew : roster s law T r γL h K σ (t.val+1)=insert (t:ℕ) S := by
      rw [roster_succ,ite_eq_left ht]
    have hM:=HeavyCenters.inner_mass_pos s law t σ hs hr hγL0
    have hd:=tier_pilot_drop hr hσ hR hγH hσH hγL hδ0 hδ hh
      (by positivity : 0≤49/Real.sqrt K) (mu_nonneg s law (t.val+1) σ)
      (ShortRoster.profile_bounds (H := H) (request s σ) r hK S) hM
      (by simpa only [qualifies,request_fin] using ht.1.2)
      (fun p=>by have hh:=ShortRoster.profile_error (request s σ) hr hK S t hbefore p; linarith)
      (fun p hp=>ShortRoster.profile_unit_drop (request s σ) hr hK S t hbefore ht.2 (by simpa only [request_fin] using hp))
      (fun p hp=>by
        have he:=ShortRoster.profile_increase_support (request s σ) hr hK S t hbefore ht.2 (by linarith :
          ShortRoster.profile (H := H) (request s σ) r K S p<ShortRoster.profile (H := H) (request s σ) r K (insert (t:ℕ) S) p)
        simpa only [request_fin] using he.2)
    change _ ≤ potential T r (mu s law (t.val+1) σ) (ShortRoster.profile (H := H) (request s σ) r K S)-
      potential T r (mu s law (t.val+1) σ) (ShortRoster.profile (H := H) (request s σ) r K (roster s law T r γL h K σ (t.val+1)))
    rw [hnew]
    exact hd
  · have hnew : roster s law T r γL h K σ (t.val+1)=S := by
      rw [roster_succ,ite_eq_right ht]
    change 0*_ ≤ potential T r (mu s law (t.val+1) σ) (ShortRoster.profile (H := H) (request s σ) r K S)-
      potential T r (mu s law (t.val+1) σ) (ShortRoster.profile (H := H) (request s σ) r K (roster s law T r γL h K σ (t.val+1)))
    rw [hnew,zero_mul,sub_self]


/-- All-step tier insertion budget against the actual finite-law optimum.
Its endpoint depends only on finite scales and k, not on the input law. -/
theorem insertion_budget (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {T : Template} {r₀ τ γH γL δH δL h : ℝ} {K : ℕ} (n p : ℕ)
    (hr : 0<r₀) (hτ : 2≤τ) (hK : 2≤K) (hσ : T.σ≤1/1000) (hR : 51201≤T.R)
    (hγH : γH≤1/100) (hσH : 10*T.σ<γH) (hγL0 : 0<γL)
    (hγL : γL≤ min (T.σ/64) (1/(1+T.L)))
    (hδH0 : 0≤δH) (hδH : δH≤1/256) (hδL0 : 0<δL) (hδL : δL≤1/4112)
    (hh : 0≤h) (hL : 8≤T.L) (hpow : 100*T.R≤γL*(2:ℝ)^p) :
    (∑ t : Fin H,avg law.val (fun σ=>∑ j∈range n,
      charge s law T (radius r₀ τ j) γH γL δH h K t σ*(128*δH*Real.exp (-h)-257*(49/Real.sqrt K)))) ≤
      driftConstant T γL δL p*(1+Real.log ((k:ℝ)+1))*
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ)+
          ∑ j∈range n,2*radius r₀ τ j*(k:ℝ) := by
  let g:=fun t σ j=>profile s law T (radius r₀ τ j) γL h K σ t
  have hrad j : 0<radius r₀ τ j := radius_pos hr (by linarith) j
  have hb:=pilot_edit_budget s law T (g := g) n p hr hτ hγL0 hγL hδL0 hδL hpow
    (by intro t σ j _ y; exact ShortRoster.profile_bounds (request s σ) _ hK _ y)
    (by
      intro t σ j _ y z
      apply (ShortRoster.profile_lipschitz (request s σ) (hrad j) hK _ y z).trans
      have hn : 0≤dist y z/radius r₀ τ j := div_nonneg dist_nonneg (hrad j).le
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right hL hn)
    (by intro t j _ y; exact profile_adapted s law T (radius r₀ τ j) γL h K t y)
  apply le_trans _ hb
  apply sum_le_sum
  intro t _
  apply sum_le_sum
  intro σ _
  by_cases hs : 0<law.val σ
  · apply mul_le_mul_of_nonneg_left _ (law.property.1 σ)
    exact sum_le_sum fun j _=>charge_le_drop s law (hrad j) hK hσ hR hγH hσH hγL0.le
      (by have hh:= (le_min_iff.mp hγL).1; linarith [T.σ_pos]) hδH0 hδH hh t σ hs
  · have hz : law.val σ=0 := le_antisymm (le_of_not_gt hs) (law.property.1 σ)
    simp [hz]

end KServer.TierProcess

end


/-! Fixed absolute tier parameters and the weighted insertion estimate.
The roster remains the chronological finite-law
roster, not a family satisfying a hypothetical insertion bound. -/
noncomputable section
open scoped BigOperators
open Finset Set
namespace KServer.TierProcess
open FiniteExperiment RankTracking PosteriorRanks Pilot Chronological
attribute [local instance] Classical.propDecidable Classical.decEq

def tierTemplate : Template where
  σ := 1/1048576
  R := 204800
  L := 8
  σ_pos := by norm_num
  σ_le := by norm_num
  R_ge := by norm_num
  L_nonneg := by norm_num

def heavyGamma : ℝ := 1/1024
def heavyDelta : ℝ := 1/8192
def tierGamma : ℝ := 1/1073741824
def tierDelta : ℝ := 1/8192

def tierK (h : ℝ) : ℕ := ⌈Real.exp (64*h)⌉₊

lemma tierK_exp (h : ℝ) : Real.exp (64*h)≤(tierK h:ℝ) := Nat.le_ceil _

lemma exp_one_ge_two : (2:ℝ)≤Real.exp 1 := by
  have hh:=Real.add_one_le_exp (1:ℝ)
  linarith

lemma tierK_ge_two {h : ℝ} (hh : 1≤h) : 2≤tierK h := by
  have he : (2:ℝ)≤Real.exp (64*h) := exp_one_ge_two.trans (Real.exp_le_exp.mpr (by linarith))
  exact_mod_cast he.trans (tierK_exp h)

lemma tierK_sqrt {h : ℝ} : Real.exp (32*h)≤Real.sqrt (tierK h) := by
  apply (Real.le_sqrt (Real.exp_nonneg _) (Nat.cast_nonneg _)).mpr
  have he : Real.exp (32*h)^2=Real.exp (64*h) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [he]
  exact tierK_exp h

lemma exp_large {h : ℝ} (hh : 1≤h) : (2:ℝ)^31≤Real.exp (31*h) := by
  calc (2:ℝ)^31 ≤ (Real.exp 1)^31 := pow_le_pow_left₀ (by norm_num) exp_one_ge_two _
       _ = Real.exp 31 := by rw [← Real.exp_nat_mul]; congr 1; norm_num
       _ ≤ Real.exp (31*h) := Real.exp_le_exp.mpr (by linarith)

lemma tier_error_absorb {h : ℝ} (hh : 1≤h) :
    257*(49/Real.sqrt (tierK h))≤64*heavyDelta*Real.exp (-h) := by
  have hKpos : 0<Real.sqrt (tierK h) := lt_of_lt_of_le (Real.exp_pos _) tierK_sqrt
  have hsq := tierK_sqrt (h := h)
  have he:=exp_large hh
  have hex : Real.exp (-h)*Real.exp (32*h)=Real.exp (31*h) := by
    rw [← Real.exp_add]; congr 1; ring
  have hmul:=mul_le_mul_of_nonneg_left hsq (Real.exp_nonneg (-h))
  rw [hex] at hmul
  have hbig : (12593:ℝ)≤64*heavyDelta*(Real.exp (-h)*Real.sqrt (tierK h)) := by
    dsimp [heavyDelta]
    nlinarith
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hKpos).mpr
  norm_num only [mul_assoc] at *
  exact hbig

lemma tier_reciprocal_absorb {h : ℝ} (hh : 1≤h) :
    1/(tierK h:ℝ)≤64*heavyDelta*Real.exp (-2*h) := by
  have hK : 0<(tierK h:ℝ) := lt_of_lt_of_le (Real.exp_pos _) (tierK_exp h)
  have he:=exp_large hh
  have h62 : (128:ℝ)≤Real.exp (62*h) := by
    have hmono : Real.exp (31*h)≤Real.exp (62*h) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hex : Real.exp (-2*h)*Real.exp (64*h)=Real.exp (62*h) := by
    rw [← Real.exp_add]; congr 1; ring
  have hmul:=mul_le_mul_of_nonneg_left (tierK_exp h) (Real.exp_nonneg (-2*h))
  rw [hex] at hmul
  apply (div_le_iff₀ hK).mpr
  dsimp [heavyDelta]
  nlinarith

lemma tier_weight_sum (n : ℕ) : (∑ i∈range n, Real.exp (-(i+1:ℝ)))≤1 := by
  have hq : Real.exp (-1)≤(1/2:ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) exp_one_ge_two
  have he (i : ℕ) : Real.exp (-(i+1:ℝ))=(Real.exp (-1))^(i+1) := by
    rw [←Real.exp_nat_mul]; congr 1; push_cast; ring
  calc _ ≤ ∑ i∈range n,(1/2:ℝ)^(i+1) := by
         apply sum_le_sum
         intro i _
         rw [he]
         exact pow_le_pow_left₀ (Real.exp_nonneg _) hq _
       _ = (1/2:ℝ)*∑ i∈range n,(1/2:ℝ)^i := by
         simp only [pow_succ,←sum_mul]; ring
       _ ≤ 1 := by nlinarith [sum_geometric_two_le n]

variable {Y : Type*} [MetricSpace Y] [Fintype Y] [DecidableEq Y]
variable {k H : ℕ} [NeZero k]

lemma weighted_insertion_drop (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {r h : ℝ} (hr : 0<r) (hh : 1≤h) (t : Fin H) (σ : Fin H → Y) (hs : 0<law.val σ) :
    charge s law tierTemplate r heavyGamma tierGamma heavyDelta h (tierK h) t σ/(tierK h:ℝ) ≤
      Real.exp (-h)*(potential tierTemplate r (mu s law (t.val+1) σ)
        (profile s law tierTemplate r tierGamma h (tierK h) σ t)-
      potential tierTemplate r (mu s law (t.val+1) σ)
        (profile s law tierTemplate r tierGamma h (tierK h) σ (t.val+1))) := by
  have hd:=charge_le_drop s law (T := tierTemplate) (γH := heavyGamma) (γL := tierGamma) (δ := heavyDelta) hr (tierK_ge_two hh)
    (by norm_num [tierTemplate]) (by norm_num [tierTemplate])
    (by norm_num [heavyGamma]) (by norm_num [tierTemplate,heavyGamma])
    (by norm_num [tierGamma]) (by norm_num [tierGamma,tierTemplate])
    (by norm_num [heavyDelta]) (by norm_num [heavyDelta]) (by linarith : 0≤h) t σ hs
  have hc:=charge_nonneg s law tierTemplate hr.le heavyGamma tierGamma heavyDelta h (tierK h) t σ
  have herr:=tier_error_absorb hh
  have hrec:=tier_reciprocal_absorb hh
  have hex : Real.exp (-h)*Real.exp (-h)=Real.exp (-2*h) := by
    rw [← Real.exp_add]; congr 1; ring
  have hlo : 64*heavyDelta*Real.exp (-h)≤128*heavyDelta*Real.exp (-h)-257*(49/Real.sqrt (tierK h)) := by linarith
  calc _ = charge s law tierTemplate r heavyGamma tierGamma heavyDelta h (tierK h) t σ*(1/(tierK h:ℝ)) := by ring
       _ ≤ charge s law tierTemplate r heavyGamma tierGamma heavyDelta h (tierK h) t σ*(64*heavyDelta*Real.exp (-2*h)) :=
         mul_le_mul_of_nonneg_left hrec hc
       _ = Real.exp (-h)*(charge s law tierTemplate r heavyGamma tierGamma heavyDelta h (tierK h) t σ*(64*heavyDelta*Real.exp (-h))) := by rw [← hex]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hlo hc).trans hd) (Real.exp_nonneg _)

/-- The constant is shared by all tiers; the overlap integer is fixed. -/
def tierDrift : ℝ := driftConstant tierTemplate tierGamma tierDelta 60

/-- A single real tier's actual insertion charges. The multiplier exp(-h)
will be summable, so the estimate does not pay the number of tiers. -/
theorem weighted_insertion_budget (s : Configuration k Y) (law : FiniteDistribution (Fin H → Y))
    {r₀ τ h : ℝ} (n : ℕ) (hr : 0<r₀) (hτ : 2≤τ) (hh : 1≤h) :
    (∑ t : Fin H,avg law.val (fun σ=>∑ j∈range n,
      charge s law tierTemplate (radius r₀ τ j) heavyGamma tierGamma heavyDelta h (tierK h) t σ/(tierK h:ℝ))) ≤
      Real.exp (-h)*(tierDrift*(1+Real.log ((k:ℝ)+1))*
        ∑ σ,law.val σ*optimalCost s (List.ofFn σ)+ ∑ j∈range n,2*radius r₀ τ j*(k:ℝ)) := by
  let g:=fun t σ j=>profile s law tierTemplate (radius r₀ τ j) tierGamma h (tierK h) σ t
  have hrad j : 0<radius r₀ τ j := radius_pos hr (by linarith) j
  have hb:=pilot_edit_budget s law tierTemplate (γ := tierGamma) (δ := tierDelta) (g := g) n 60 hr hτ
    (by norm_num [tierGamma]) (by norm_num [tierGamma,tierTemplate])
    (by norm_num [tierDelta]) (by norm_num [tierDelta])
    (by norm_num [tierTemplate,tierGamma])
    (by intro t σ j _ y; exact ShortRoster.profile_bounds (request s σ) _ (tierK_ge_two hh) _ y)
    (by intro t σ j _ y z; simpa only [g,profile,tierTemplate,mul_div_assoc] using ShortRoster.profile_lipschitz (H := H) (request s σ) (hrad j) (tierK_ge_two hh) (roster s law tierTemplate (radius r₀ τ j) tierGamma h (tierK h) σ t) y z)
    (by intro t j _ y; exact profile_adapted s law tierTemplate (radius r₀ τ j) tierGamma h (tierK h) t y)
  have hpoint : (∑ t : Fin H,avg law.val (fun σ=>∑ j∈range n,
      charge s law tierTemplate (radius r₀ τ j) heavyGamma tierGamma heavyDelta h (tierK h) t σ/(tierK h:ℝ))) ≤
    ∑ t : Fin H,avg law.val (fun σ=>∑ j∈range n,Real.exp (-h)*
      (potential tierTemplate (radius r₀ τ j) (mu s law (t.val+1) σ) (g t σ j)-
      potential tierTemplate (radius r₀ τ j) (mu s law (t.val+1) σ) (g (t.val+1) σ j))) := by
    apply sum_le_sum
    intro t _
    apply sum_le_sum
    intro σ _
    by_cases hs : 0<law.val σ
    · apply mul_le_mul_of_nonneg_left _ (law.property.1 σ)
      exact sum_le_sum fun j _=>weighted_insertion_drop s law (hrad j) hh t σ hs
    · have hz : law.val σ=0 := le_antisymm (le_of_not_gt hs) (law.property.1 σ)
      simp [hz]
  refine hpoint.trans ?_
  simp only [← mul_sum]
  simp only [avg,mul_left_comm (law.val _) (Real.exp (-h)),← mul_sum]
  exact mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (-h))

end KServer.TierProcess

end


noncomputable section
open scoped BigOperators
open Finset
namespace KServer.Chronological
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y]

lemma schedule_mem (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop)
    (n i : ℕ) : i∈schedule center r K qualifies n ↔
      i<n ∧ insertTest center (schedule center r K qualifies i) r K i (qualifies i) := by
  induction n with
  | zero => simp [schedule]
  | succ n ih =>
    by_cases hin : i=n
    · subst i
      have hn : n∉schedule center r K qualifies n := fun hh=>Nat.lt_irrefl _ (schedule_before _ _ _ _ _ _ hh)
      simp only [schedule]
      split_ifs with he
      · simp [he]
      · simp [he,hn]
    · simp only [schedule]
      split_ifs with h
      · rw [mem_insert,or_iff_right hin,ih]
        constructor
        · intro hh; exact ⟨by omega,hh.2⟩
        · intro hh; exact ⟨by omega,hh.2⟩
      · rw [ih]
        constructor
        · intro hh; exact ⟨by omega,hh.2⟩
        · intro hh; exact ⟨by omega,hh.2⟩

lemma schedule_mono (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop) :
    Monotone (schedule center r K qualifies) := by
  intro m n hmn i hi
  rw [schedule_mem] at hi ⊢
  exact ⟨hi.1.trans_le hmn,hi.2⟩

lemma age_mono_history (center : ℕ → Y) {I J : Finset ℕ} (hIJ : I⊆J) (R : ℝ) (i : ℕ) :
    age center I R i≤age center J R i := by
  apply card_le_card
  exact filter_subset_filter _ hIJ

variable [Fintype Y]

def reserved (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop) (t : ℕ) : Finset ℕ :=
  young center (schedule center r K qualifies t) (20*r) (K^2)

lemma reserved_card (center : ℕ → Y) {r : ℝ} (hr : 0≤r) (K : ℕ) (qualifies : ℕ → Prop) (t : ℕ) :
    (reserved center r K qualifies t).card ≤ Fintype.card Y*K^2 :=
  reserved_count center _ (by positivity) _

omit [Fintype Y] in
lemma reserved_before (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop) (t i : ℕ)
    (hi : i∈reserved center r K qualifies t) : i<t :=
  schedule_before _ _ _ _ _ _ ((mem_young _ _ _ _ _).mp hi).1

omit [Fintype Y] in
lemma reserved_backward (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop)
    {i t T : ℕ} (htT : t≤T) (hit : i<t) (hi : i∈reserved center r K qualifies T) :
    i∈reserved center r K qualifies t := by
  obtain ⟨hI,ha⟩ := (mem_young _ _ _ _ _).mp hi
  apply (mem_young _ _ _ _ _).mpr
  refine ⟨?_,(age_mono_history center (schedule_mono center r K qualifies htT) _ _).trans_lt ha⟩
  rw [schedule_mem] at hI ⊢
  exact ⟨hit,hI.2⟩

/-- Reservation is deterministic and persists even after a random retirement.
The previous prefix is also excluded, giving the stipulated one-step cooldown. -/
def conflicts (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop) (t : ℕ) : Finset ℕ :=
  reserved center r K qualifies t ∪ reserved center r K qualifies (t-1)

def pool (Y : Type*) [Fintype Y] (K : ℕ) : ℕ := 4*(Fintype.card Y*K^2)+4

omit [MetricSpace Y] in
lemma pool_pos (K : ℕ) : 0<pool Y K := by dsimp [pool]; omega

lemma conflicts_card (center : ℕ → Y) {r : ℝ} (hr : 0≤r) (K : ℕ) (qualifies : ℕ → Prop) (t : ℕ) :
    (conflicts center r K qualifies t).card<pool Y K := by
  have h := card_union_le (reserved center r K qualifies t) (reserved center r K qualifies (t-1))
  have h1 := reserved_card center hr K qualifies t
  have h2 := reserved_card center hr K qualifies (t-1)
  dsimp [conflicts,pool]
  omega

omit [Fintype Y] in
lemma conflicts_before (center : ℕ → Y) (r : ℝ) (K : ℕ) (qualifies : ℕ → Prop)
    (t i : ℕ) (hi : i∈conflicts center r K qualifies t) : i<t := by
  rcases mem_union.mp hi with hi|hi
  · exact reserved_before center r K qualifies t i hi
  · exact (reserved_before center r K qualifies (t-1) i hi).trans_le (Nat.sub_le _ _)

/-- Actual permanent record labels in the finite source pool. -/
def label (center : ℕ → Y) {r : ℝ} (hr : 0≤r) (K : ℕ) (qualifies : ℕ → Prop) (i : ℕ) : Fin (pool Y K) :=
  OnlineLabels.color (pool_pos K) (conflicts center r K qualifies) (conflicts_card center hr K qualifies) i

/-- Common labels on consecutive maps identify the same chronological record.
In particular ordinary roster anchors do not move when a label persists. -/
theorem label_injective_consecutive (center : ℕ → Y) {r : ℝ} (hr : 0≤r) (K : ℕ)
    (qualifies : ℕ → Prop) (t : ℕ) :
    Set.InjOn (label center hr K qualifies)
      (↑(reserved center r K qualifies t ∪ reserved center r K qualifies (t+1)) : Set ℕ) := by
  apply OnlineLabels.color_injective_on (pool_pos K) _ (conflicts_card center hr K qualifies)
    (conflicts_before center r K qualifies)
  intro i hi j hj hji
  have hiT : i<t+1 := by
    rcases mem_union.mp hi with hi|hi
    · exact (reserved_before center r K qualifies t i hi).trans (Nat.lt_succ_self _)
    · exact reserved_before center r K qualifies (t+1) i hi
  apply mem_union_left
  rcases mem_union.mp hj with hj|hj
  · exact reserved_backward center r K qualifies (by omega) hji hj
  · exact reserved_backward center r K qualifies (by omega) hji hj

end KServer.Chronological

end


/-! Present chronological balls, permanent finite-pool labels and actual
anchors. These are literal constructed keys, not assumed partitions. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierKeys
open Chronological ActualRoster FiniteBallLaw PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y] {H K : ℕ}

def key (center : ℕ → Y) {r : ℝ} (hr : 0≤r) (K : ℕ) (q : ℕ → Prop)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (t : ℕ) (x : Y) :
    Option (Fin (pool Y K)) :=
  (first center (schedule center r K q t) r life rad x).map
    (fun i : Fin H=>Chronological.label center hr K q i)

lemma key_some (center : ℕ → Y) {r : ℝ} (hr : 0≤r) (q : ℕ → Prop)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (t : ℕ) (x : Y) (a : Fin (pool Y K)) :
    key center hr K q life rad t x=some a →
      ∃ i : Fin H,first center (schedule center r K q t) r life rad x=some i ∧
        Chronological.label center hr K q i=a := by
  unfold key
  cases he : first center (schedule center r K q t) r life rad x with
  | none => simp
  | some i => intro hh; exact ⟨i,rfl,Option.some.inj hh⟩

lemma first_reserved (center : ℕ → Y) (r : ℝ) (q : ℕ → Prop)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (t : ℕ) (x : Y) {i : Fin H}
    (hi : first center (schedule center r K q t) r life rad x=some i) :
    (i:ℕ)∈reserved center r K q t := by
  have hp:=((first_some_iff _ _ _ _ _ _ _).mp hi).1.1
  exact (mem_young _ _ _ _ _).mpr (present_young center _ r life i hp)

lemma common_same_record (center : ℕ → Y) {r : ℝ} (hr : 0≤r) (q : ℕ → Prop)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (t : ℕ) (x y : Y)
    {i j : Fin H}
    (hi : first center (schedule center r K q t) r life rad x=some i)
    (hj : first center (schedule center r K q (t+1)) r life rad y=some j)
    (he : Chronological.label center hr K q i=Chronological.label center hr K q j) : i=j := by
  apply Fin.ext
  exact label_injective_consecutive center hr K q t
    (mem_union_left _ (first_reserved center r q life rad t x hi))
    (mem_union_right _ (first_reserved center r q life rad (t+1) y hj)) he

variable [Nonempty Y]

def anchor (center : ℕ → Y) {r : ℝ} (hr : 0≤r) (K : ℕ) (q : ℕ → Prop)
    (t : ℕ) (a : Fin (pool Y K)) : Y :=
  if he : ∃ i∈reserved center r K q t,Chronological.label center hr K q i=a
  then center he.choose else Classical.arbitrary Y

lemma anchor_record (center : ℕ → Y) {r : ℝ} (hr : 0≤r) (q : ℕ → Prop)
    (t : ℕ) {i : ℕ} (hi : i∈reserved center r K q t) :
    anchor center hr K q t (Chronological.label center hr K q i)=center i := by
  have he : ∃ j∈reserved center r K q t,
      Chronological.label center hr K q j=Chronological.label center hr K q i := ⟨i,hi,rfl⟩
  rw [anchor,dite_eq_left he]
  congr 1
  exact label_injective_consecutive center hr K q t
    (mem_union_left _ he.choose_spec.1) (mem_union_left _ hi) he.choose_spec.2

lemma anchor_distance (center : ℕ → Y) {r : ℝ} (hr : 0<r) (q : ℕ → Prop)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (t : ℕ) (x : Y)
    {a : Fin (pool Y K)} (ha : key center hr.le K q life rad t x=some a) :
    dist (anchor center hr.le K q t a) x≤2*r := by
  obtain ⟨i,hi,hl⟩:=key_some center hr.le q life rad t x a ha
  rw [←hl,anchor_record center hr.le q t (first_reserved center r q life rad t x hi)]
  exact ((first_some_iff _ _ _ _ _ _ _).mp hi).1.2 |>.trans (radius_range hr _).2

lemma anchors_persist (center : ℕ → Y) {r : ℝ} (hr : 0≤r) (q : ℕ → Prop)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) (t : ℕ) (x y : Y)
    {a : Fin (pool Y K)} (hx : key center hr K q life rad t x=some a)
    (hy : key center hr K q life rad (t+1) y=some a) :
    anchor center hr K q t a=anchor center hr K q (t+1) a := by
  obtain ⟨i,hi,hli⟩:=key_some center hr q life rad t x a hx
  obtain ⟨j,hj,hlj⟩:=key_some center hr q life rad (t+1) y a hy
  have he:=common_same_record center hr q life rad t x y hi hj (hli.trans hlj.symm)
  subst j
  rw [←hli,anchor_record center hr q t (first_reserved center r q life rad t x hi),
    anchor_record center hr q (t+1) (first_reserved center r q life rad (t+1) y hj)]

omit [Nonempty Y] in
lemma guaranteed_coverage (center : ℕ → Y) {r : ℝ} (hr : 0<r) (hK : 0<K)
    (q : ℕ → Prop) (t : ℕ) (ht : t<H) (hq : q t)
    (life : Fin H → Lifetime K) (rad : Fin H → Outcome Y r) :
    ∃ a,key center hr.le K q life rad (t+1) (center t)=some a := by
  obtain ⟨i,hi⟩:=qualified_covered center hr hK q t ht hq life rad
  have hn : first center (schedule center r K q (t+1)) r life rad (center t)≠none := by
    intro hh
    exact (first_none_iff _ _ _ _ _ _).mp hh i hi
  cases he : first center (schedule center r K q (t+1)) r life rad (center t) with
  | none => exact False.elim (hn he)
  | some i => exact ⟨Chronological.label center hr.le K q i,by simp only [key,he,Option.map_some]⟩

omit [Nonempty Y] in
theorem spatial_bound (center : ℕ → Y) {r : ℝ} (hr : 0<r) (hK : 1≤K)
    (q : ℕ → Prop) (life : Fin H → Lifetime K) (t : ℕ) (x y : Y) (hxy : dist x y≤r) :
    probability (fun _ : Fin H=>law (Y:=Y) (Real.log (1+(K:ℝ)^2)) r)
      (fun rad=>key center hr.le K q life rad t x≠key center hr.le K q life rad t y)≤
      2*Real.log (1+(K:ℝ)^2)*dist x y/r := by
  have hl : 0<Real.log (1+(K:ℝ)^2) := Real.log_pos (by
    have hk : (1:ℝ)≤K := by exact_mod_cast hK
    nlinarith)
  exact (ActualRoster.probability_mono (fun (_ : Fin H) d=>law_nonneg hl hr d) (by
    intro rad hne he
    exact hne (congrArg (Option.map (fun i : Fin H=>Chronological.label center hr.le K q i)) he))).trans
      (ActualRoster.spatial_bound center (schedule center r K q t) hr hK life x y hxy)
end KServer.TierKeys

end


/-! Fixed finite precedence alphabets: literal selection of the first covering
structure, with singleton fallback. This is the coordinate map in §07. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.PriorityKeys
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I Y : Type*} [Fintype I] [LinearOrder I] {A : I → Type*}

def covered (key : (i:I) → Y → Option (A i)) (x : Y) : Finset I :=
  univ.filter (fun i=>key i x≠none)

def selected (key : (i:I) → Y → Option (A i)) (x : Y) : Option (Sigma A) :=
  if h:(covered key x).Nonempty then
    let i:=(covered key x).min' h
    (key i x).map (fun a=>⟨i,a⟩)
  else none

lemma selected_some_of_mem (key : (i:I) → Y → Option (A i)) (x : Y)
    (h:(covered key x).Nonempty) :
    ∃ a : A ((covered key x).min' h),
      key ((covered key x).min' h) x=some a ∧
      selected key x=some ⟨(covered key x).min' h,a⟩ := by
  have hn:=(mem_filter.mp (min'_mem (covered key x) h)).2
  cases he:key ((covered key x).min' h) x with
  | none => exact False.elim (hn he)
  | some a => exact ⟨a,rfl,by simp only [selected,dite_eq_left h,he,Option.map_some]⟩

lemma selected_none_iff (key : (i:I) → Y → Option (A i)) (x : Y) :
    selected key x=none ↔ ∀ i,key i x=none := by
  constructor
  · intro he i
    by_contra hn
    have h:(covered key x).Nonempty:=⟨i,mem_filter.mpr ⟨mem_univ _,hn⟩⟩
    obtain ⟨a,_,ha⟩:=selected_some_of_mem key x h
    rw [he] at ha
    cases ha
  · intro hh
    have he:¬(covered key x).Nonempty:=by
      intro h
      obtain ⟨i,hi⟩:=h
      exact (mem_filter.mp hi).2 (hh i)
    simp only [selected,dite_eq_right he]

lemma selected_some (key : (i:I) → Y → Option (A i)) (x : Y)
    {z : Sigma A} (hz:selected key x=some z) :
    key z.1 x=some z.2 ∧ ∀ i<z.1,key i x=none := by
  have h:(covered key x).Nonempty:=by
    by_contra hn
    simp only [selected,dite_eq_right hn] at hz
    cases hz
  obtain ⟨a,ha,hs⟩:=selected_some_of_mem key x h
  have he: (⟨(covered key x).min' h,a⟩:Sigma A)=z:=Option.some.inj (hs.symm.trans hz)
  subst z
  refine ⟨ha,?_⟩
  intro i hi
  by_contra hn
  have hm:=min'_le (covered key x) i (mem_filter.mpr ⟨mem_univ _,hn⟩)
  exact (not_lt_of_ge hm) hi

lemma selected_eq_of_prefix (key : (i:I) → Y → Option (A i)) (x y : Y)
    (h : I) (hx:key h x≠none) (he:∀ i≤h,key i x=key i y) :
    selected key x=selected key y := by
  have hcx:(covered key x).Nonempty:=⟨h,mem_filter.mpr ⟨mem_univ _,hx⟩⟩
  have hy:key h y≠none:=by rw [←he h le_rfl]; exact hx
  have hcy:(covered key y).Nonempty:=⟨h,mem_filter.mpr ⟨mem_univ _,hy⟩⟩
  have hmx:(covered key x).min' hcx≤h:=min'_le (covered key x) h (mem_filter.mpr ⟨mem_univ _,hx⟩)
  have hmy:(covered key y).min' hcy≤h:=min'_le (covered key y) h (mem_filter.mpr ⟨mem_univ _,hy⟩)
  obtain ⟨a,ha,hsa⟩:=selected_some_of_mem key x hcx
  obtain ⟨b,hb,hsb⟩:=selected_some_of_mem key y hcy
  have hxy:(covered key x).min' hcx≤(covered key y).min' hcy:=by
    apply min'_le
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rw [he _ hmy,hb]
    exact Option.some_ne_none b
  have hyx:(covered key y).min' hcy≤(covered key x).min' hcx:=by
    apply min'_le
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rw [←he _ hmx,ha]
    exact Option.some_ne_none a
  have hh:=le_antisymm hxy hyx
  rw [selected,dite_eq_left hcx,selected,dite_eq_left hcy]
  dsimp only
  exact (congrArg (fun i => (key i x).map (fun a => (⟨i,a⟩:Sigma A))) hh).trans
    (congrArg (Option.map (fun a => (⟨(covered key y).min' hcy,a⟩:Sigma A))) (he _ hmy))

def key (keys : (i:I) → Y → Option (A i)) (x : Y) : Sigma A ⊕ Y :=
  match selected keys x with
  | some z=>Sum.inl z
  | none=>Sum.inr x

lemma key_ne_prefix (keys : (i:I) → Y → Option (A i)) (x y : Y)
    (h:I) (hx:keys h x≠none) (hne:key keys x≠key keys y) :
    ∃ i≤h,keys i x≠keys i y := by
  by_contra hn
  push Not at hn
  have he:=selected_eq_of_prefix keys x y h hx hn
  have hc:(covered keys x).Nonempty:=⟨h,mem_filter.mpr ⟨mem_univ _,hx⟩⟩
  obtain ⟨a,_,ha⟩:=selected_some_of_mem keys x hc
  exact hne (by simp only [key,←he,ha])

theorem probability_prefix_bound {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ ω,0≤w ω)
    (keys : Ω → (i:I) → Y → Option (A i)) (x y : Y) (h:I)
    (hx : ∀ ω,keys ω h x≠none) :
    (∑ ω,if key (keys ω) x≠key (keys ω) y then w ω else 0)≤
      ∑ i∈univ.filter (fun i=>i≤h),∑ ω,if keys ω i x≠keys ω i y then w ω else 0 := by
  rw [sum_comm]
  apply sum_le_sum
  intro ω _
  by_cases he:key (keys ω) x=key (keys ω) y
  · simp only [he,ne_eq,not_true_eq_false,ite_false]
    exact sum_nonneg (fun i _=>by split_ifs <;> first | exact hw ω | exact le_rfl)
  · obtain ⟨i,hi,hd⟩:=key_ne_prefix (keys ω) x y h (hx ω) he
    rw [ite_eq_left he]
    calc w ω = (if keys ω i x≠keys ω i y then w ω else 0) := (ite_eq_left hd).symm
         _ ≤ ∑ j∈univ.filter (fun i=>i≤h),if keys ω j x≠keys ω j y then w ω else 0 :=
           single_le_sum (f:=fun j=>if keys ω j x≠keys ω j y then w ω else 0)
             (s:=univ.filter (fun j=>j≤h)) (fun j _=>by split_ifs <;> first | exact hw ω | exact le_rfl)
             (mem_filter.mpr ⟨mem_univ _,hi⟩)

variable [MetricSpace Y]

def anchor (anchors : (i:I) → A i → Y) : Sigma A ⊕ Y → Y
  | Sum.inl z=>anchors z.1 z.2
  | Sum.inr x=>x

lemma anchor_distance (keys : (i:I) → Y → Option (A i))
    (anchors : (i:I) → A i → Y) {r:ℝ} (hr:0≤r)
    (ha:∀ i x a,keys i x=some a → dist (anchors i a) x≤20*r) (x:Y) :
    dist (anchor anchors (key keys x)) x≤20*r := by
  cases he:selected keys x with
  | none => simpa only [key,he,anchor,dist_self] using mul_nonneg (by norm_num : (0:ℝ)≤20) hr
  | some z =>
    simpa only [key,he,anchor] using ha z.1 x z.2 (selected_some keys x he).1

lemma cell_diameter (keys : (i:I) → Y → Option (A i))
    (anchors : (i:I) → A i → Y) {r:ℝ} (hr:0≤r)
    (ha:∀ i x a,keys i x=some a → dist (anchors i a) x≤20*r)
    {x y:Y} (he:key keys x=key keys y) : dist x y≤40*r := by
  have hx:=anchor_distance keys anchors hr ha x
  have hy:=anchor_distance keys anchors hr ha y
  rw [←he] at hy
  have ht:=dist_triangle x (anchor anchors (key keys x)) y
  rw [dist_comm x (anchor anchors (key keys x))] at ht
  linarith
end KServer.PriorityKeys

end


/-! Literal dyadic tier parameters and their logarithmic expense, §07. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.TierDyadic
open TierProcess

lemma exists_power (L:ℝ) : ∃ n:ℕ,L≤(2:ℝ)^n := by
  obtain ⟨n,hn⟩:=exists_nat_gt L
  refine ⟨n,hn.le.trans ?_⟩
  exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le

def index (L:ℝ) : ℕ := Nat.find (exists_power L)

lemma index_covers (L:ℝ) : L≤(2:ℝ)^(index L) := Nat.find_spec (exists_power L)

lemma index_le {L:ℝ} {n:ℕ} (hn:L≤(2:ℝ)^n) : index L≤n := Nat.find_min' _ hn

lemma index_zero {L:ℝ} (hL:L≤1) : index L=0 := by
  apply Nat.eq_zero_of_le_zero
  exact index_le (by simpa only [pow_zero] using hL)

lemma preceding_lt (L:ℝ) {n:ℕ} (hn : n < index L) : (2:ℝ)^n<L :=
  lt_of_not_ge (Nat.find_min (exists_power L) hn)

lemma tier_sum (n:ℕ) : ∑ i∈range (n+1),(2:ℝ)^i=2*(2:ℝ)^n-1 := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [sum_range_succ,ih,pow_succ]; ring

theorem qualified_sum {L:ℝ} (hL:0≤L) :
    ∑ i∈range (index L+1),(2:ℝ)^i≤4*(1+L) := by
  by_cases hz:index L=0
  · rw [hz,tier_sum,pow_zero]; linarith
  · have hp:=preceding_lt L (Nat.sub_one_lt hz)
    have hs:(index L-1)+1=index L:=by omega
    have hh:(2:ℝ)^(index L)<2*L:=by
      rw [←hs,pow_succ]
      linarith
    rw [tier_sum]
    linarith

lemma index_mono : Monotone index := by
  intro a b hab
  exact index_le (hab.trans (index_covers b))

lemma tierK_upper {h:ℝ} (hh:1≤h) : (tierK h:ℝ)≤2*Real.exp (64*h) := by
  have he : 1≤Real.exp (64*h):=Real.one_le_exp_iff.mpr (by linarith)
  have hc : (tierK h:ℝ)<Real.exp (64*h)+1 := by
    exact Nat.ceil_lt_add_one (Real.exp_nonneg _)
  linarith

lemma exp_three_ge_five : (5:ℝ)≤Real.exp 3 := by
  have h2:=exp_one_ge_two
  have hpow : (2:ℝ)^3≤(Real.exp 1)^3:=pow_le_pow_left₀ (by norm_num) h2 _
  rw [←Real.exp_nat_mul] at hpow
  norm_num at hpow
  linarith

theorem radius_coefficient {h:ℝ} (hh:1≤h) :
    Real.log (1+(tierK h:ℝ)^2)≤131*h := by
  have hk:=tierK_upper hh
  have he : 1≤Real.exp (128*h):=Real.one_le_exp_iff.mpr (by linarith)
  have hex:(Real.exp (64*h))^2=Real.exp (128*h):=by
    rw [←Real.exp_nat_mul]; congr 1; ring
  have hb : 1+(tierK h:ℝ)^2≤5*Real.exp (128*h):=by
    nlinarith [(Nat.cast_nonneg (tierK h) : (0:ℝ)≤tierK h),Real.exp_pos (64*h)]
  have h5 : (5:ℝ)≤Real.exp (3*h):=exp_three_ge_five.trans (Real.exp_le_exp.mpr (by linarith))
  have hc : 1+(tierK h:ℝ)^2≤Real.exp (131*h):=by
    calc _ ≤ 5*Real.exp (128*h) := hb
         _ ≤ Real.exp (3*h)*Real.exp (128*h) := mul_le_mul_of_nonneg_right h5 (Real.exp_nonneg _)
         _ = Real.exp (131*h) := by rw [←Real.exp_add]; congr 1; ring
  exact (Real.log_le_iff_le_exp (by positivity)).mpr hc
end KServer.TierDyadic

end


/-! Coverage and exact tier selection for the actual posterior-driven map.
The logarithmic ratio is computed from the new true-prefix metric posterior. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelCoverage
open FiniteExperiment Pilot TierProcess
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y] {k H : ℕ} [NeZero k]

lemma ball_mass_mono (μ:Y→ℝ) (hμ:∀ y,0 ≤ μ y) (x:Y) {r R:ℝ} (hr:r ≤ R) :
    mass μ (ball x r) ≤ mass μ (ball x R) := by
  exact sum_le_sum_of_subset_of_nonneg
    (fun y hy=> mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2.trans hr⟩)
    (fun y _ _=> hμ y)

lemma ball_mass_total (μ:Y→ℝ) (hμ:∀ y,0 ≤ μ y) (x:Y) (r:ℝ) :
    mass μ (ball x r) ≤ ∑ y,μ y :=
  sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun y _ _=> hμ y)

lemma ball_mass_served (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) {r:ℝ} (hr:0 ≤ r) :
    1 ≤ mass (mu s law (t.val+1) σ) (ball (σ t) r) := by
  apply (mu_served s law t σ hs).trans
  exact single_le_sum (fun y _=> mu_nonneg s law (t.val+1) σ y)
    (by simp only [ball,mem_filter,mem_univ,true_and,dist_self]; exact hr)

def logratio (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (t:Fin H) (r:ℝ) : ℝ :=
  Real.log (mass (mu s law (t.val+1) σ) (ball (σ t) (100*tierTemplate.R*r)) /
    mass (mu s law (t.val+1) σ) (ball (σ t) (tierGamma*r)))

lemma logratio_bounds (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) {r:ℝ} (hr:0 ≤ r) :
    0 ≤ logratio s law σ t r ∧ logratio s law σ t r ≤ Real.log k := by
  have hi:=ball_mass_served s law σ hs t (mul_nonneg (by norm_num [tierGamma] : 0 ≤ tierGamma) hr)
  have hb:=ball_mass_mono (mu s law (t.val+1) σ) (mu_nonneg s law (t.val+1) σ)
    (σ t) (show tierGamma*r ≤ 100*tierTemplate.R*r by dsimp [tierGamma,tierTemplate]; nlinarith)
  have ht:=ball_mass_total (mu s law (t.val+1) σ) (mu_nonneg s law (t.val+1) σ)
    (σ t) (100*tierTemplate.R*r)
  rw [mu_total s law (t.val+1) σ hs] at ht
  have hip:0 < mass (mu s law (t.val+1) σ) (ball (σ t) (tierGamma*r)):=by linarith
  have hp:0 < mass (mu s law (t.val+1) σ) (ball (σ t) (100*tierTemplate.R*r)):=by linarith
  have hq:1 ≤ mass (mu s law (t.val+1) σ) (ball (σ t) (100*tierTemplate.R*r))/
      mass (mu s law (t.val+1) σ) (ball (σ t) (tierGamma*r)) := (le_div_iff₀ hip).mpr (by simpa using hb)
  refine ⟨Real.log_nonneg hq,Real.log_le_log (div_pos hp hip) ?_⟩
  apply (div_le_iff₀ hip).mpr
  exact ht.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) hi)

lemma qualifies_of_log (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) {r h:ℝ} (hr:0 ≤ r)
    (hh:logratio s law σ t r ≤ h) :
    qualifies s law tierTemplate r tierGamma h σ t := by
  refine ⟨t.isLt,?_⟩
  rw [request_fin]
  have hi:=ball_mass_served s law σ hs t (mul_nonneg (by norm_num [tierGamma] : 0 ≤ tierGamma) hr)
  have hb:=ball_mass_served s law σ hs t
    (mul_nonneg (by norm_num [tierTemplate] : 0 ≤ 100*tierTemplate.R) hr : 0 ≤ 100*tierTemplate.R*r)
  have hip:0 < mass (mu s law (t.val+1) σ) (ball (σ t) (tierGamma*r)):=by linarith
  have hbp:0 < mass (mu s law (t.val+1) σ) (ball (σ t) (100*tierTemplate.R*r)):=by linarith
  exact (div_le_iff₀ hip).mp ((Real.log_le_iff_le_exp (div_pos hbp hip)).mp hh)

def firstTier (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (t:Fin H) (r:ℝ) : ℕ := TierDyadic.index (logratio s law σ t r)

lemma firstTier_le (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) {r:ℝ} (hr:0 ≤ r) :
    firstTier s law σ t r ≤ TierDyadic.index (Real.log k) :=
  TierDyadic.index_mono (logratio_bounds s law σ hs t hr).2

lemma firstTier_qualifies (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (hs:0 < law.val σ) (t:Fin H) {r:ℝ} (hr:0 ≤ r) :
    qualifies s law tierTemplate r tierGamma ((2:ℝ)^(firstTier s law σ t r)) σ t :=
  qualifies_of_log s law σ hs t hr (TierDyadic.index_covers _)

lemma heavy_near_center (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (t:Fin H) {r γ δ:ℝ} (hr:0 ≤ r)
    (hh:mass (mu s law (t.val+1) σ) (ball (σ t) (51200*r)) ≤ 
      (1+δ)*mass (mu s law (t.val+1) σ) (ball (σ t) (γ*r))) :
    ∃ a∈HeavyCenters.centers s law r γ δ σ (t.val+1),dist a (σ t) ≤ 8*r := by
  rw [HeavyCenters.centers_succ,HeavyCenters.step]
  split_ifs with ha
  · exact ⟨σ t,mem_insert_self _ _,by simpa only [dist_self] using mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hr⟩
  · have hn:¬∀ a∈HeavyCenters.centers s law r γ δ σ t.val,8*r < dist a (σ t):=fun hn=> ha ⟨hh,hn⟩
    push Not at hn
    exact hn

lemma heavy_agrees (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (σ:Fin H→Y) (t:Fin H) {r γ δ:ℝ} (hr:0 < r)
    (hh:mass (mu s law (t.val+1) σ) (ball (σ t) (51200*r)) ≤ 
      (1+δ)*mass (mu s law (t.val+1) σ) (ball (σ t) (γ*r)))
    (rad:Fin H→FiniteUniform.Outcome Y r) (y:Y) (hy:4*dist (σ t) y < r) :
    ∃ a,HeavyKeys.key s law r γ δ σ rad (t.val+1) (σ t)=some a ∧
      HeavyKeys.key s law r γ δ σ rad (t.val+1) y=some a := by
  obtain ⟨a,ha,hd⟩:=heavy_near_center s law σ t hr.le hh
  have hv:=HeavySchedule.run_valid s law hr γ δ σ rad (t.val+1)
  have hC:=HeavyCenters.centers_separated s law r γ δ σ (t.val+1)
  have hx:dist a (σ t) ≤ (HeavySchedule.run s law r γ δ σ rad (t.val+1)).rad a:=by linarith [(hv.1 a ha).1]
  have hz:dist a y ≤ (HeavySchedule.run s law r γ δ σ rad (t.val+1)).rad a:=by
    linarith [dist_triangle a (σ t) y,(hv.1 a ha).1,dist_nonneg (x:=σ t) (y:=y)]
  have hkx:=(HeavyKeys.centerKey_some hr hC (fun b hb=> (hv.1 b hb).2)).mpr ⟨ha,hx⟩
  have hky:=(HeavyKeys.centerKey_some hr hC (fun b hb=> (hv.1 b hb).2)).mpr ⟨ha,hz⟩
  refine ⟨(HeavySchedule.run s law r γ δ σ rad (t.val+1)).label a,?_,?_⟩  <;> 
    simp only [HeavyKeys.key,hkx,hky,Option.map_some]
end KServer.LevelCoverage

end


/-! The actual finite complete level alphabet and map of §07: chronological
heavy balls precede the dyadic tiers, and singleton keys are the fallback. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelKeys
open FiniteExperiment Pilot TierProcess LevelCoverage
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y : Type*} [MetricSpace Y] [Fintype Y] {k H : ℕ} [NeZero k]

abbrev Tier (k:ℕ) := Fin (TierDyadic.index (Real.log k)+1)
abbrev Structure (k:ℕ) := WithBot (Tier k)

def height (i:Tier k) : ℝ := (2:ℝ)^i.val
omit [NeZero k] in
lemma height_ge (i:Tier k) : 1 ≤ height i := one_le_pow₀ (by norm_num)

abbrev Alphabet (Y:Type*) [Fintype Y] (k:ℕ) : Structure k → Type _
  | none => HeavyLabels.Pool Y
  | some i => Fin (Chronological.pool Y (tierK (height i)))

abbrev Key (Y:Type*) [Fintype Y] (k:ℕ) := (Sigma (Alphabet Y k)) ⊕ Y

abbrev Tape (Y:Type*) [MetricSpace Y] [Fintype Y] (k H:ℕ) (r:ℝ) :=
  (Fin H → FiniteUniform.Outcome Y r) ×
    ((i:Tier k) → (Fin H → ActualRoster.Lifetime (tierK (height i))) ×
      (Fin H → FiniteBallLaw.Outcome Y r))

def tierQualifies (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (r:ℝ) (σ:Fin H→Y) (i:Tier k) : ℕ → Prop :=
  qualifies s law tierTemplate r tierGamma (height i) σ

def keys (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) :
    (i:Structure k) → Y → Option (Alphabet Y k i)
  | none => HeavyKeys.key s law r heavyGamma heavyDelta σ tape.1 t
  | some i => TierKeys.key (request s σ) hr (tierK (height i))
      (tierQualifies s law r σ i) (tape.2 i).1 (tape.2 i).2 t

def map (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (x:Y) : Key Y k :=
  PriorityKeys.key (keys s law hr σ tape t) x

lemma covered_request (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (hs:0 < law.val σ) (tape:Tape Y k H r) (t:Fin H) :
    ∃ i:Structure k,keys s law hr.le σ tape (t.val+1) i (σ t) ≠ none := by
  let i:Tier k:=⟨firstTier s law σ t r,by have hh:=firstTier_le s law σ hs t hr.le; omega⟩
  have hq:tierQualifies s law r σ i t:=firstTier_qualifies s law σ hs t hr.le
  obtain ⟨a,ha⟩:=TierKeys.guaranteed_coverage (request s σ) hr
    (lt_of_lt_of_le (by omega : 0 < 2) (tierK_ge_two (height_ge i)))
    (tierQualifies s law r σ i) t t.isLt hq (tape.2 i).1 (tape.2 i).2
  refine ⟨some i,?_⟩
  change TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i)
    (tape.2 i).1 (tape.2 i).2 (t.val+1) (σ t) ≠ none
  rw [request_fin] at ha
  rw [ha]
  exact Option.some_ne_none _

def heavyAnchor (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    (r:ℝ) (σ:Fin H→Y) (tape:Fin H→FiniteUniform.Outcome Y r) (t:ℕ) (a:HeavyLabels.Pool Y) : Y :=
  if h:∃ c∈HeavyCenters.centers s law r heavyGamma heavyDelta σ t,
    (HeavySchedule.run s law r heavyGamma heavyDelta σ tape t).label c=a
  then h.choose else s 0

lemma heavy_anchor_distance (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Fin H→FiniteUniform.Outcome Y r) (t:ℕ) (x:Y)
    (a:HeavyLabels.Pool Y) (ha:HeavyKeys.key s law r heavyGamma heavyDelta σ tape t x=some a) :
    dist (heavyAnchor s law r σ tape t a) x ≤ 20*r := by
  have hv:=HeavySchedule.run_valid s law hr heavyGamma heavyDelta σ tape t
  unfold HeavyKeys.key at ha
  cases hc:HeavyKeys.centerKey (HeavyCenters.centers s law r heavyGamma heavyDelta σ t)
    (HeavySchedule.run s law r heavyGamma heavyDelta σ tape t).rad x with
  | none => simp only [hc,Option.map_none] at ha; cases ha
  | some c =>
    simp only [hc,Option.map_some,Option.some.injEq] at ha
    have hC:=HeavyCenters.centers_separated s law r heavyGamma heavyDelta σ t
    obtain ⟨hcm,hd⟩:=(HeavyKeys.centerKey_some hr hC (fun b hb=>(hv.1 b hb).2)).mp hc
    have he:∃ b∈HeavyCenters.centers s law r heavyGamma heavyDelta σ t,
      (HeavySchedule.run s law r heavyGamma heavyDelta σ tape t).label b=a:=⟨c,hcm,ha⟩
    rw [heavyAnchor,dite_eq_left he]
    have hh:=hv.2 he.choose_spec.1 hcm (he.choose_spec.2.trans ha.symm)
    rw [hh]
    exact hd.trans (hv.1 c hcm).2

omit [MetricSpace Y] [Fintype Y] in
private theorem nonemptyY (s:Configuration k Y) : Nonempty Y := ⟨s 0⟩

def anchors (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) :
    (i:Structure k) → Alphabet Y k i → Y
  | none => heavyAnchor s law r σ tape.1 t
  | some i => @TierKeys.anchor Y _ _ (nonemptyY s) (request s σ) r hr
      (tierK (height i)) (tierQualifies s law r σ i) t

lemma structure_anchor_distance (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ)
    (i:Structure k) (x:Y) (a:Alphabet Y k i)
    (ha:keys s law hr.le σ tape t i x=some a) :
    dist (anchors s law hr.le σ tape t i a) x ≤ 20*r := by
  cases i with
  | none => exact heavy_anchor_distance s law hr σ tape.1 t x a ha
  | some i =>
    have : Nonempty Y :=nonemptyY s
    have hd:=TierKeys.anchor_distance (request s σ) hr (tierQualifies s law r σ i)
      (tape.2 i).1 (tape.2 i).2 t x ha
    exact hd.trans (by linarith)

def anchor (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 ≤ r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) : Key Y k → Y :=
  PriorityKeys.anchor (anchors s law hr σ tape t)

lemma anchor_distance (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (x:Y) :
    dist (anchor s law hr.le σ tape t (map s law hr.le σ tape t x)) x ≤ 20*r :=
  PriorityKeys.anchor_distance _ _ hr.le (structure_anchor_distance s law hr σ tape t) x

lemma cell_diameter (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (tape:Tape Y k H r) (t:ℕ) (x y:Y)
    (he:map s law hr.le σ tape t x=map s law hr.le σ tape t y) : dist x y ≤ 40*r :=
  PriorityKeys.cell_diameter _ _ hr.le (structure_anchor_distance s law hr σ tape t) he
end KServer.LevelKeys

end


/-! Explicit finite independent tapes and their exact marginal laws. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.FiniteTape
open PartitionProbabilities
attribute [local instance] Classical.propDecidable Classical.decEq

variable {I:Type*} [Fintype I] {Ω:I→Type*} [∀ i,Fintype (Ω i)]

lemma marginal (w:(i:I)→Ω i→ℝ) (hw:∀ i,∑ a,w i a=1) (j:I) (f:Ω j→ℝ) :
    (∑ o,productWeight w o*f (o j))=∑ a,w j a*f a := by
  let g:(i:I)→Ω i→ℝ:=fun i a=>if h:i=j then f (h ▸ a) else 1
  have hg (o:(i:I)→Ω i):∏ i,g i (o i)=f (o j):=by simp [g]
  have he:=product_expectation w g
  simp only [hg] at he
  rw [he]
  trans ∏ i,if i=j then (∑ a,w j a*f a) else 1
  · apply prod_congr rfl
    intro i _
    by_cases hi:i=j
    · subst i; simp [g]
    · simp [g,hi,hw]
  · simp

lemma event_marginal (w:(i:I)→Ω i→ℝ) (hw:∀ i,∑ a,w i a=1) (j:I) (E:Ω j→Prop) :
    probability w (fun o=>E (o j))=∑ a,if E a then w j a else 0 := by
  have hh:=marginal w hw j (fun a=>if E a then 1 else 0)
  simpa only [probability,mul_ite,mul_one,mul_zero] using hh

variable {A B:Type*} [Fintype A] [Fintype B]

def pair (u:A→ℝ) (v:B→ℝ) (p:A×B) : ℝ := u p.1*v p.2

omit [Fintype A] [Fintype B] in
lemma pair_nonneg {u:A→ℝ} {v:B→ℝ} (hu:∀ a,0 ≤ u a) (hv:∀ b,0 ≤ v b) (p:A×B) :
    0 ≤ pair u v p := mul_nonneg (hu _) (hv _)

lemma pair_sum (u:A→ℝ) (v:B→ℝ) (hu:∑ a,u a=1) (hv:∑ b,v b=1) :
    ∑ p,pair u v p=1 := by simp only [pair,Fintype.sum_prod_type,←mul_sum,hv,mul_one,hu]

lemma pair_left (u:A→ℝ) (v:B→ℝ) (hv:∑ b,v b=1) (f:A→ℝ) :
    (∑ p,pair u v p*f p.1)=∑ a,u a*f a := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro a _
  simp only [pair]
  calc (∑ b,u a*v b*f a)=(u a*f a)*∑ b,v b := by rw [mul_sum]; apply sum_congr rfl; intros; ring
       _ = _ := by rw [hv,mul_one]

lemma pair_right (u:A→ℝ) (v:B→ℝ) (hu:∑ a,u a=1) (f:B→ℝ) :
    (∑ p,pair u v p*f p.2)=∑ b,v b*f b := by
  simp only [Fintype.sum_prod_type,pair,mul_assoc,←mul_sum,←sum_mul,hu,one_mul]

lemma pair_event_left (u:A→ℝ) (v:B→ℝ) (hv:∑ b,v b=1) (E:A→Prop) :
    (∑ p,if E p.1 then pair u v p else 0)=∑ a,if E a then u a else 0 := by
  simpa only [mul_ite,mul_one,mul_zero] using pair_left u v hv (fun a=>if E a then 1 else 0)

lemma pair_event_right (u:A→ℝ) (v:B→ℝ) (hu:∑ a,u a=1) (E:B→Prop) :
    (∑ p,if E p.2 then pair u v p else 0)=∑ b,if E b then v b else 0 := by
  simpa only [mul_ite,mul_one,mul_zero] using pair_right u v hu (fun b=>if E b then 1 else 0)
end KServer.FiniteTape

end


/-! A single genuine finite independent tape for the complete level map. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.LevelLaw
open LevelKeys FiniteTape PartitionProbabilities FiniteExperiment TierProcess
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
abbrev RequestLaw (Y:Type*) [Fintype Y] (H:ℕ) := FiniteDistribution (Fin H→Y)
local instance (priority := 2000) finDecEq (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {Y:Type*} [MetricSpace Y] [Fintype Y] {k H:ℕ}

def heavyWeight (r:ℝ) (a:Fin H→FiniteUniform.Outcome Y r) : ℝ :=
  productWeight (fun _ : Fin H=>FiniteUniform.law r) a

def lifetimeWeight (i:Tier k) (a:Fin H→ActualRoster.Lifetime (tierK (height i))) : ℝ :=
  productWeight (fun _ : Fin H=>ActualRoster.lifetimeLaw (tierK (height i))) a

def radiusWeight (r:ℝ) (i:Tier k) (a:Fin H→FiniteBallLaw.Outcome Y r) : ℝ :=
  productWeight (fun _ : Fin H=>FiniteBallLaw.law (Real.log (1+(tierK (height i):ℝ)^2)) r) a

def tierWeight (r:ℝ) (i:Tier k) :
    (Fin H→ActualRoster.Lifetime (tierK (height i))) × (Fin H→FiniteBallLaw.Outcome Y r)→ℝ :=
  pair (lifetimeWeight i) (radiusWeight r i)

def weight (r:ℝ) : Tape Y k H r→ℝ :=
  pair (heavyWeight r) (productWeight (tierWeight r))

lemma heavy_sum {r:ℝ} (hr:0 < r) : (∑ a:Fin H→FiniteUniform.Outcome Y r,heavyWeight r a)=1 :=
  productWeight_sum (fun _ : Fin H=>FiniteUniform.law (Y:=Y) r) (fun _=>FiniteUniform.law_sum hr)

lemma lifetime_sum (i:Tier k) : (∑ a:Fin H→ActualRoster.Lifetime (tierK (height i)),lifetimeWeight i a)=1 :=
  productWeight_sum (fun _ : Fin H=>ActualRoster.lifetimeLaw (tierK (height i)))
    (fun _=>ActualRoster.lifetime_sum (by have hh:=tierK_ge_two (height_ge i); omega))

lemma log_pos (i:Tier k) : 0 < Real.log (1+(tierK (height i):ℝ)^2) := by
  have hn:=tierK_ge_two (height_ge i)
  have hr : (2:ℝ) ≤ tierK (height i) := by exact_mod_cast hn
  apply Real.log_pos
  nlinarith

lemma radius_sum {r:ℝ} (hr:0 < r) (i:Tier k) :
    (∑ a:Fin H→FiniteBallLaw.Outcome Y r,radiusWeight r i a)=1 :=
  productWeight_sum (fun _ : Fin H=>FiniteBallLaw.law (Y:=Y) (Real.log (1+(tierK (height i):ℝ)^2)) r)
    (fun _=>FiniteBallLaw.law_sum (log_pos i) hr)

lemma tier_sum {r:ℝ} (hr:0 < r) (i:Tier k) : ∑ a,tierWeight (Y:=Y) (H:=H) r i a=1 :=
  pair_sum (lifetimeWeight (H:=H) i) (radiusWeight (Y:=Y) (H:=H) r i) (lifetime_sum i) (radius_sum hr i)

lemma weight_sum {r:ℝ} (hr:0 < r) : ∑ a: Tape Y k H r,weight r a=1 :=
  pair_sum (heavyWeight (Y:=Y) (H:=H) r) (productWeight (tierWeight (Y:=Y) (H:=H) (k:=k) r))
    (heavy_sum hr) (productWeight_sum _ (tier_sum hr))

lemma heavy_nonneg {r:ℝ} (hr:0 < r) (a:Fin H→FiniteUniform.Outcome Y r) : 0 ≤ heavyWeight r a :=
  productWeight_nonneg (fun (_:Fin H) b=>FiniteUniform.law_nonneg hr b) a

lemma lifetime_nonneg (i:Tier k) (a:Fin H→ActualRoster.Lifetime (tierK (height i))) :
    0 ≤ lifetimeWeight i a :=
  productWeight_nonneg (fun (_:Fin H) b=>ActualRoster.lifetime_nonneg
    (by have hh:=tierK_ge_two (height_ge i); omega) b) a

lemma radius_nonneg {r:ℝ} (hr:0 < r) (i:Tier k) (a:Fin H→FiniteBallLaw.Outcome Y r) :
    0 ≤ radiusWeight r i a :=
  productWeight_nonneg (fun (_:Fin H) b=>FiniteBallLaw.law_nonneg (log_pos i) hr b) a

lemma tier_nonneg {r:ℝ} (hr:0 < r) (i:Tier k) (a:(Fin H→ActualRoster.Lifetime (tierK (height i))) × (Fin H→FiniteBallLaw.Outcome Y r)) :
    0 ≤ tierWeight r i a := mul_nonneg (lifetime_nonneg i a.1) (radius_nonneg hr i a.2)

lemma weight_nonneg {r:ℝ} (hr:0 < r) (a:Tape Y k H r) : 0 ≤ weight r a :=
  mul_nonneg (heavy_nonneg hr a.1) (productWeight_nonneg (tier_nonneg hr) a.2)

lemma heavy_event {r:ℝ} (hr:0 < r) (E:(Fin H→FiniteUniform.Outcome Y r)→Prop) :
    (∑ a:Tape Y k H r,if E a.1 then weight r a else 0)=
      probability (fun _ : Fin H=>FiniteUniform.law r) E :=
  pair_event_left (heavyWeight (Y:=Y) (H:=H) r) (productWeight (tierWeight (Y:=Y) (H:=H) (k:=k) r))
    (productWeight_sum _ (tier_sum hr)) E

lemma tier_event {r:ℝ} (hr:0 < r) (i:Tier k)
    (E:((Fin H→ActualRoster.Lifetime (tierK (height i))) × (Fin H→FiniteBallLaw.Outcome Y r))→Prop) :
    (∑ a:Tape Y k H r,if E (a.2 i) then weight r a else 0)=∑ b,if E b then tierWeight r i b else 0 := by
  have he:=pair_event_right (heavyWeight (Y:=Y) (H:=H) r)
    (productWeight (tierWeight (Y:=Y) (H:=H) (k:=k) r)) (heavy_sum hr) (fun a=>E (a i))
  exact he.trans (event_marginal (tierWeight r) (tier_sum hr) i E)

variable [NeZero k]

lemma heavy_spatial (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (t:ℕ) (x y:Y) (hxy:4*dist x y < r) :
    (∑ a:Tape Y k H r,if keys s law hr.le σ a t none x≠keys s law hr.le σ a t none y then weight r a else 0)
      ≤ dist x y/(4*r) := by
  change (∑ a:Tape Y k H r,if HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 t x≠
    HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 t y then weight r a else 0) ≤ _
  have he:=heavy_event (k:=k) hr (fun a=>HeavyKeys.key s law r heavyGamma heavyDelta σ a t x≠
    HeavyKeys.key s law r heavyGamma heavyDelta σ a t y)
  have heq : (∑ a:Tape Y k H r,if HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 t x≠
    HeavyKeys.key s law r heavyGamma heavyDelta σ a.1 t y then weight r a else 0)=
    probability (fun _ : Fin H=>FiniteUniform.law r) (fun a=>HeavyKeys.key s law r heavyGamma heavyDelta σ a t x≠
    HeavyKeys.key s law r heavyGamma heavyDelta σ a t y) := by
      refine Eq.trans ?_ he
      apply sum_congr rfl
      intro a _
      split_ifs <;> rfl
  rw [heq]
  exact HeavyKeys.spatial_bound s law hr heavyGamma heavyDelta σ t x y hxy

lemma tier_spatial (s:Configuration k Y) (law:RequestLaw Y H)
    {r:ℝ} (hr:0 < r) (σ:Fin H→Y) (t:ℕ) (i:Tier k) (x y:Y) (hxy:dist x y ≤ r) :
    (∑ a:Tape Y k H r,if keys s law hr.le σ a t (some i) x≠keys s law hr.le σ a t (some i) y then weight r a else 0)
      ≤ 2*Real.log (1+(tierK (height i):ℝ)^2)*dist x y/r := by
  change (∑ a:Tape Y k H r,if TierKeys.key (request s σ) hr.le (tierK (height i))
      (tierQualifies s law r σ i) (a.2 i).1 (a.2 i).2 t x≠
      TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i)
      (a.2 i).1 (a.2 i).2 t y then weight r a else 0) ≤ _
  have he:=tier_event (H:=H) hr i (fun a=>TierKeys.key (request s σ) hr.le (tierK (height i))
      (tierQualifies s law r σ i) a.1 a.2 t x≠
      TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i) a.1 a.2 t y)
  have heq : (∑ a:Tape Y k H r,if TierKeys.key (request s σ) hr.le (tierK (height i))
      (tierQualifies s law r σ i) (a.2 i).1 (a.2 i).2 t x≠
      TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i)
      (a.2 i).1 (a.2 i).2 t y then weight r a else 0)=
      ∑ b:(Fin H→ActualRoster.Lifetime (tierK (height i))) × (Fin H→FiniteBallLaw.Outcome Y r),if TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i) b.1 b.2 t x≠
        TierKeys.key (request s σ) hr.le (tierK (height i)) (tierQualifies s law r σ i) b.1 b.2 t y
        then tierWeight r i b else 0 := by
    refine Eq.trans ?_ (he.trans ?_)
    all_goals
      apply sum_congr rfl
      intro a _
      split_ifs <;> rfl
  rw [heq]
  simp only [tierWeight,Fintype.sum_prod_type,pair]
  trans ∑ life:Fin H→ActualRoster.Lifetime (tierK (height i)),
    lifetimeWeight i life*(2*Real.log (1+(tierK (height i):ℝ)^2)*dist x y/r)
  · apply sum_le_sum
    intro life _
    simp_rw [show ∀ rad, (if TierKeys.key (request s σ) hr.le (tierK (height i))
      (tierQualifies s law r σ i) life rad t x≠TierKeys.key (request s σ) hr.le (tierK (height i))
      (tierQualifies s law r σ i) life rad t y then lifetimeWeight i life*radiusWeight r i rad else 0)=
      lifetimeWeight i life*(if TierKeys.key (request s σ) hr.le (tierK (height i))
        (tierQualifies s law r σ i) life rad t x≠TierKeys.key (request s σ) hr.le (tierK (height i))
        (tierQualifies s law r σ i) life rad t y then radiusWeight r i rad else 0) by intro rad; split_ifs <;> simp]
    rw [←mul_sum]
    apply mul_le_mul_of_nonneg_left
    · convert TierKeys.spatial_bound (request s σ) hr
        (by have hh:=tierK_ge_two (height_ge i); omega) (tierQualifies s law r σ i) life t x y hxy using 1
      all_goals first | rfl | (apply sum_congr rfl; intro a _; split_ifs <;> rfl)
    · exact lifetime_nonneg i life
  · rw [←sum_mul,lifetime_sum,one_mul]
end KServer.LevelLaw

end

end OAI
