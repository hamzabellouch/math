import OAI.Probability.CriticalZ3.Extension

namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

open Filter Topology
namespace CriticalScales

noncomputable def contourError : ℝ := (1/100 : ℝ)^7/2

theorem contourError_pos : 0 < contourError := by norm_num [contourError]
theorem contourError_lt_half : contourError < 1/2 := by norm_num [contourError]

theorem contour_power (n : ℕ) :
    (2*contourError)^((n : ℝ)/7) = (1/100 : ℝ)^n := by
  have he : 2*contourError = (1/100 : ℝ)^7 := by unfold contourError; ring
  rw [he,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1/100)]
  have hn : (7 : ℝ)*((n : ℝ)/7) = n := by ring
  norm_num only [Nat.cast_ofNat]
  rw [hn,Real.rpow_natCast]

theorem contour_budget :
    (∑' n : ℕ, 2*(n : ℝ)*3^n*(2*contourError)^((n : ℝ)/7)) < 1 := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(3/100 : ℝ)‖ < 1)).mul_left 2
  have he (n : ℕ) : 2*(n : ℝ)*3^n*(2*contourError)^((n : ℝ)/7) =
      2*((n : ℝ)*(3/100 : ℝ)^n) := by
    rw [contour_power]
    have hb : (3/100 : ℝ)^n = 3^n*(1/100 : ℝ)^n := by rw [←mul_pow]; congr 1; ring
    rw [hb]
    ring
  simp_rw [he]
  rw [h.tsum_eq]
  norm_num

theorem error_budgets {f : ℝ} (hf0 : 0 < f) (hf1 : f < 1) :
    ∃ δ η τ γ : ℝ,
      δ ∈ Set.Ioo 0 1 ∧ η ∈ Set.Ioo 0 1 ∧ τ ∈ Set.Ioo 0 1 ∧ γ ∈ Set.Ioo 0 1 ∧
      δ+52*η/δ < f ∧ τ < η/4 ∧ γ < δ ∧ 2*γ/τ < η/4 := by
  let δ := f/2
  let η := δ*f/208
  let τ := η/8
  let γ := min (δ/2) (τ*η/16)
  have hd0 : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ < 1 := by dsimp [δ]; linarith
  have he0 : 0 < η := by dsimp [η]; positivity
  have he1 : η < 1 := by dsimp [η]; nlinarith
  have ht0 : 0 < τ := by dsimp [τ]; positivity
  have ht1 : τ < 1 := by dsimp [τ]; linarith
  have hg0 : 0 < γ := lt_min (by positivity) (by positivity)
  have hgd : γ ≤ δ/2 := min_le_left _ _
  have hge : γ ≤ τ*η/16 := min_le_right _ _
  refine ⟨δ,η,τ,γ,⟨hd0,hd1⟩,⟨he0,he1⟩,⟨ht0,ht1⟩,⟨hg0,by linarith⟩,?_,?_,?_,?_⟩
  · have heq : 52*η/δ = f/4 := by dsimp [η]; field_simp; ring
    rw [heq]
    dsimp [δ]
    linarith
  · dsimp [τ]; linarith
  · linarith
  · apply (div_lt_iff₀ ht0).mpr
    nlinarith

end CriticalScales

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace Model
noncomputable def law : (m : Model) → ℝ → Measure m.Config
  | .bond,p => bondLaw p
  | .site,p => siteLaw p

def InfiniteAt : (m : Model) → Vertex → Set m.Config
  | .bond,x => bondInfiniteAt x
  | .site,x => siteInfiniteAt x

def SeedInfinite : (m : Model) → Vertex → ℕ → Set m.Config
  | .bond,c,r => bondSeedInfinite c r
  | .site,c,r => siteSeedInfinite c r

instance law_probability (m : Model) (p : ℝ) : IsProbabilityMeasure (m.law p) := by
  cases m <;> dsimp [law] <;> infer_instance

theorem law_eq_product (m : Model) (p : ℝ) :
    m.law p = ProductCylinder.law (fun _ => parameter p) := by cases m <;> rfl

theorem law_coe_eq_product (m : Model) (q : Set.Icc (0 : ℝ) 1) :
    m.law q = ProductCylinder.law (fun _ => q) := by
  rw [law_eq_product]
  have h : parameter (q : ℝ) = q := Subtype.ext (parameter_coe q.property)
  rw [h]

theorem exists_seed (m : Model) {p ε : ℝ} (hp : 0 < m.law p (m.InfiniteAt 0)) (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧ (m.law p).real (m.SeedInfinite 0 r)ᶜ < ε^24 := by
  cases m
  · exact exists_bondSeed hp hε
  · exact exists_siteSeed hp hε

theorem lower_quarterFaces (m : Model) {p γ : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    {r : ℕ} (hseed : (m.law p).real (m.SeedInfinite 0 r)ᶜ < (γ/2)^24)
    (s : Finset ℕ) (hs : ∀ n ∈ s, r ≤ n) :
    ∃ q ∈ Set.Ioo (p/2) p, ∀ n ∈ s, ∀ c f,
      1-γ < (m.law q).real (m.SeedReaches c r n (QuarterFace c n f)) := by
  cases m
  · simpa only [law,seedReaches_bond] using bond_lower_quarterFaces hp hγ hseed s hs
  · exact site_lower_quarterFaces hp hγ hseed s hs
end Model

structure ScaleData (model : Model) where
  p : ℝ
  p_pos : 0 < p
  p_lt_one : p < 1
  q : Set.Icc (0 : ℝ) 1
  q_half : p/2 < (q : ℝ)
  q_lt : (q : ℝ) < p
  δ : ℝ
  η : ℝ
  τ : ℝ
  γ : ℝ
  δ_range : δ ∈ Set.Ioo 0 1
  η_range : η ∈ Set.Ioo 0 1
  τ_range : τ ∈ Set.Ioo 0 1
  γ_range : γ ∈ Set.Ioo 0 1
  failure_budget : δ+52*η/δ < CriticalScales.contourError
  relay_budget : τ < η/4
  γδ : γ < δ
  trial_budget : 2*γ/τ < η/4
  seed : ℕ
  K : ℕ
  R : ℕ
  r : ℕ
  seed_pos : 0 < seed
  K_pos : 0 < K
  seed_R : seed < R
  large_r : 100*(R+1) < r
  K_budget : 4/((K:ℝ)*(p/2)^(Box.seedCard model seed+1)) < η/4
  R_budget : 1/((1-p)^(K*(8*seed+5)^3)*(R-seed:ℕ)) < η/4
  faces : ∀ n ∈ ({2*r,2*r+1,10*r} : Finset ℕ), ∀ c f,
    1-γ < (ProductCylinder.law (fun _ : model.Bit => q)).real
      (model.SeedReaches c seed n (QuarterFace c n f))

theorem exists_scales (model : Model) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hInf : 0 < model.law p (model.InfiniteAt 0)) : ∃ s : ScaleData model, s.p = p := by
  obtain ⟨δ,η,τ,γ,hδ,hη,hτ,hγ,hb,hτb,hγδ,hγb⟩ := CriticalScales.error_budgets
    CriticalScales.contourError_pos (CriticalScales.contourError_lt_half.trans (by norm_num))
  obtain ⟨a,ha,hseed⟩ := model.exists_seed hInf (show 0 < γ/2 by linarith [hγ.1])
  let ρ : ℝ := (p/2)^(Box.seedCard model a+1)
  have hρ : 0 < ρ := pow_pos (by linarith) _
  obtain ⟨K,hK⟩ := exists_nat_gt (16/(ρ*η))
  have hK0 : 0 < K := by
    have : 0 < (K:ℝ) := (div_pos (by norm_num) (mul_pos hρ hη.1)).trans hK
    exact_mod_cast this
  have hKb : 4/((K:ℝ)*ρ) < η/4 := by
    have hh := (div_lt_iff₀ (mul_pos hρ hη.1)).mp hK
    apply (div_lt_iff₀ (mul_pos (by exact_mod_cast hK0) hρ)).mpr
    nlinarith
  let α : ℝ := (1-p)^(K*(8*a+5)^3)
  have hα : 0 < α := pow_pos (by linarith) _
  obtain ⟨d,hd⟩ := exists_nat_gt (4/(α*η))
  have hd0 : 0 < d := by
    have : 0 < (d:ℝ) := (div_pos (by norm_num) (mul_pos hα hη.1)).trans hd
    exact_mod_cast this
  let R := a+d
  have haR : a < R := by dsimp [R]; omega
  have hRb : 1/(α*(R-a:ℕ)) < η/4 := by
    have hh := (div_lt_iff₀ (mul_pos hα hη.1)).mp hd
    have he : R-a = d := by dsimp [R]; omega
    rw [he]
    apply (div_lt_iff₀ (mul_pos hα (by exact_mod_cast hd0))).mpr
    nlinarith
  let r := 100*(R+1)+1
  have hlr : 100*(R+1) < r := by dsimp [r]; omega
  have har : a ≤ r := by omega
  obtain ⟨q,hq,hfaces⟩ := model.lower_quarterFaces hp hγ.1 hseed
    {2*r,2*r+1,10*r} (by intro n hn; simp only [Finset.mem_insert,Finset.mem_singleton] at hn; omega)
  let q' : Set.Icc (0:ℝ) 1 := ⟨q,⟨by linarith [hq.1],le_of_lt (hq.2.trans hp1)⟩⟩
  refine ⟨⟨p,hp,hp1,q',hq.1,hq.2,δ,η,τ,γ,hδ,hη,hτ,hγ,hb,hτb,hγδ,hγb,
    a,K,R,r,ha,hK0,haR,hlr,hKb,hRb,?_⟩,rfl⟩
  intro n hn c f
  have hh := hfaces n hn c f
  rw [show q = (q':ℝ) from rfl,model.law_coe_eq_product q'] at hh
  exact hh

namespace ScaleData
variable {model : Model} (s : ScaleData model)

theorem q_pos : 0 < (s.q:ℝ) := (half_pos s.p_pos).trans s.q_half

theorem successCard_le : Box.successCard model s.seed ≤ Box.seedCard model s.seed+1 := by
  cases model <;> simp [Box.successCard]

theorem success_bound : (s.p/2)^(Box.seedCard model s.seed+1) ≤
    (s.q:ℝ)^Box.successCard model s.seed := by
  exact (pow_le_pow_left₀ (by linarith [s.p_pos]) s.q_half.le _).trans
    (pow_le_pow_of_le_one s.q.property.1 s.q.property.2 s.successCard_le)

theorem extension_budget :
    1/((1-s.p)^(s.K*(8*s.seed+5)^3)*(s.R-s.seed:ℕ)) +
      4/((s.K:ℝ)*(s.q:ℝ)^Box.successCard model s.seed)+2*s.γ/s.τ+s.τ < s.η := by
  have hh : 4/((s.K:ℝ)*(s.q:ℝ)^Box.successCard model s.seed) ≤
      4/((s.K:ℝ)*(s.p/2)^(Box.seedCard model s.seed+1)) := by
    apply div_le_div_of_nonneg_left (by norm_num)
      (mul_pos (by exact_mod_cast s.K_pos) (pow_pos (half_pos s.p_pos) _))
    exact mul_le_mul_of_nonneg_left s.success_bound (Nat.cast_nonneg _)
  linarith [s.R_budget,s.K_budget,s.trial_budget,s.relay_budget]
end ScaleData
end CriticalZ3

end OAI
