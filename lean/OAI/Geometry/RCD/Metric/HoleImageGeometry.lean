import OAI.Geometry.RCD.Metric.HoleBallVolumeCover
import OAI.Geometry.RCD.Sobolev.FiniteDisjointIntegral

namespace OAI

/-! # Pulling separated holes back and detecting a missing image ball -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem hole_pullback_disjoint {X ι : Type*} [MetricSpace X] {n : ℕ}
    {u : X → Euclidean n} {Ω : Set X} {C L : ℝ} (hC : 0 < C)
    (hlip : ∀ x ∈ Ω, ∀ y ∈ Ω, dist (u x) (u y) ≤ C*dist x y)
    {z : ι → X} {c : ι → Euclidean n} {r s : ι → ℝ}
    (hz : ∀ i, z i ∈ Ω) (hsub : ∀ i, ball (z i) (s i) ⊆ Ω)
    (htouch : ∀ i, dist (u (z i)) (c i)=r i)
    (hroom : ∀ i, C*s i+r i ≤ L*r i)
    (hdisj : Pairwise (fun i j => Disjoint (ball (c i) (L*r i)) (ball (c j) (L*r j)))) :
    Pairwise (fun i j => Disjoint (ball (z i) (s i)) (ball (z j) (s j))) := by
  have himage (i : ι) {x : X} (hx : x ∈ ball (z i) (s i)) :
      u x ∈ ball (c i) (L*r i) := by
    have hd := hlip x (hsub i hx) (z i) (hz i)
    have hx' : dist x (z i) < s i := hx
    have hh := dist_triangle (u x) (u (z i)) (c i)
    rw [htouch i] at hh
    have hstrict := mul_lt_mul_of_pos_left hx' hC
    exact mem_ball.mpr (by linarith [hroom i])
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  exact Set.disjoint_left.mp (hdisj hij) (himage i hxi) (himage j hxj)

theorem missing_ball_obstructs_coordinates {X : Type*} [MetricSpace X] {n : ℕ}
    {u : X → Euclidean n} {z : X} {c : Euclidean n} {r ε : ℝ}
    (hr : 0 < r) (hε : ε < 1/4)
    (htouch : dist (u z) c = r)
    (hmiss : ∀ x ∈ ball z r, u x ∉ ball c r) :
    ¬IsPointedApproximation z 0 r (1/2) ε (fun x => r⁻¹ • (u x-u z)) := by
  intro happ
  let d := c-u z
  have hd : ‖d‖=r := by simpa only [d,dist_eq_norm,norm_sub_rev] using htouch
  let w := r⁻¹ • ((1/4:ℝ) • d)
  have hw : ‖w‖=(1/4:ℝ) := by
    simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),
      abs_of_pos (by norm_num : (0:ℝ)<1/4),hd]
    field_simp
  obtain ⟨x,hx,hxw⟩ := happ.2.2 w (by rw [dist_zero_right,hw]; linarith)
  have hxr : x ∈ ball z r := by
    change dist x z < r
    linarith
  have hxnear : dist (u x-u z) ((1/4:ℝ) • d) ≤ r*ε := by
    calc
      _ = dist (r • (r⁻¹ • (u x-u z))) (r • w) := by
        simp only [w,smul_smul,← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul,one_smul]
      _ = r*dist (r⁻¹ • (u x-u z)) w := by
        rw [dist_smul₀,Real.norm_of_nonneg hr.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left hxw hr.le
  have hquarter : dist ((1/4:ℝ) • d) d=(3/4:ℝ)*r := by
    rw [dist_eq_norm,show (1/4:ℝ) • d-d=(-(3/4:ℝ)) • d by module,norm_smul,hd]
    norm_num
  have huin : u x ∈ ball c r := by
    have hh := dist_triangle (u x-u z) ((1/4:ℝ) • d) d
    rw [hquarter] at hh
    change dist (u x) c < r
    have he : dist (u x-u z) d=dist (u x) c := by
      exact dist_sub_right (u x) c (u z)
    rw [he] at hh
    nlinarith [mul_lt_mul_of_pos_left hε hr]
  exact hmiss x hxr huin

theorem finite_hole_defect_bound {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) {Ω : Set X} {f : X → ℝ} {B : ι → Set X} {r : ι → ℝ}
    {n : ℕ} {b : ℝ} (hb : 0 < b) (hf : IntegrableOn f Ω μ)
    (hf0 : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ f x)
    (hBm : ∀ i, MeasurableSet (B i)) (hBsub : ∀ i, B i ⊆ Ω)
    (hdisj : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hcharge : ∀ i, b*(r i)^n ≤ ∫ x in B i, f x ∂μ) :
    (∑ i, (r i)^n) ≤ (∫ x in Ω, f x ∂μ)/b := by
  apply (le_div_iff₀ hb).mpr
  calc
    _ = ∑ i, b*(r i)^n := by rw [mul_comm,Finset.mul_sum]
    _ ≤ ∑ i, ∫ x in B i, f x ∂μ := Finset.sum_le_sum (fun i _ => hcharge i)
    _ ≤ _ := finite_disjoint_setIntegral_le μ hf hf0 hBm hBsub hdisj

end RegularPointCoordinates

end

end OAI
