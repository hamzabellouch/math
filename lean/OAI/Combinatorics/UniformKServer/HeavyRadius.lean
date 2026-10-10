import Mathlib
import OAI.Combinatorics.UniformKServer.FiniteThreshold

namespace OAI

                                  
section

/-! A finite exact realization of the uniform heavy-ball radius.  The same
finite signature records membership for every possible center. Thus selecting
a center by the input-driven schedule does not alter the radius distribution. -/
noncomputable section
namespace UniformKServer.HeavyRadius
open FiniteProbability
open scoped Classical
variable {X : Type*} [Fintype X] [MetricSpace X]
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

def probability (r : ℝ) (a : X × X) : ℝ := max 0 (min 1 ((20*r-dist a.1 a.2)/(4*r)))

omit [Fintype X] in
theorem probability_bounds (r : ℝ) (a : X × X) : probability r a ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

abbrev Sample (r : ℝ) := FiniteThreshold.Signature (@probability X _ r)

def law (r : ℝ) : Law (Sample (X:=X) r) := FiniteThreshold.experiment (probability r : X × X → ℝ)

def scalar (r : ℝ) (ω : Sample (X:=X) r) : ℝ := Classical.choose ω.property

omit [Fintype X] in
theorem scalar_mem (r : ℝ) (ω : Sample (X:=X) r) : scalar r ω ∈ Set.Ioc (0:ℝ) 1 :=
  (Classical.choose_spec ω.property).1

omit [Fintype X] in
theorem signature_eq (r : ℝ) (ω : Sample (X:=X) r) :
    ω.val=FiniteThreshold.threshold (probability r) (scalar r ω) :=
  (Classical.choose_spec ω.property).2

def radius (r : ℝ) (ω : Sample (X:=X) r) : ℝ := 20*r-4*r*scalar r ω

omit [Fintype X] in
theorem radius_bounds (r : ℝ) (hr : 0 ≤ r) (ω : Sample (X:=X) r) :
    radius r ω ∈ Set.Icc (16*r) (20*r) := by
  have h := scalar_mem r ω
  dsimp [radius]
  constructor <;> nlinarith [h.1,h.2]

omit [Fintype X] in
theorem covers (r : ℝ) (hr : 0 < r) (ω : Sample (X:=X) r) (c p : X) :
    ω.val (c,p)=true ↔ dist c p ≤ radius r ω := by
  rw [signature_eq]
  simp only [FiniteThreshold.threshold,decide_eq_true_eq,probability,le_max_iff,le_min_iff]
  have hu := scalar_mem r ω
  rw [or_iff_right (not_le_of_gt hu.1),and_iff_right hu.2,le_div_iff₀ (by positivity : 0 < 4*r)]
  dsimp [radius]
  constructor <;> intro h <;> linarith

omit [Fintype X] in
theorem probability_lipschitz (r : ℝ) (hr : 0 < r) (c x y : X) :
    |probability r (c,x)-probability r (c,y)| ≤ dist x y/(4*r) := by
  have hmax := abs_max_sub_max_le_max (0:ℝ) (min 1 ((20*r-dist c x)/(4*r)))
    0 (min 1 ((20*r-dist c y)/(4*r)))
  have hmin := abs_min_sub_min_le_max (1:ℝ) ((20*r-dist c x)/(4*r))
    1 ((20*r-dist c y)/(4*r))
  rw [sub_self,abs_zero,max_eq_right (abs_nonneg (min 1 ((20*r-dist c x)/(4*r))-min 1 ((20*r-dist c y)/(4*r))))] at hmax
  rw [sub_self,abs_zero,max_eq_right (abs_nonneg ((20*r-dist c x)/(4*r)-(20*r-dist c y)/(4*r)))] at hmin
  have hd : |dist c y-dist c x| ≤ dist x y := by
    simpa only [dist_comm] using abs_dist_sub_le y x c
  calc
    _ ≤ |(20*r-dist c x)/(4*r)-(20*r-dist c y)/(4*r)| := hmax.trans hmin
    _ = |dist c y-dist c x|/(4*r) := by
      rw [←sub_div,show (20*r-dist c x)-(20*r-dist c y)=dist c y-dist c x by ring,
        abs_div,abs_of_pos (by positivity : 0 < 4*r)]
    _ ≤ _ := div_le_div_of_nonneg_right hd (by positivity)

theorem separation (r : ℝ) (hr : 0 < r) (c x y : X) :
    (law r).expect (fun ω => if ω.val (c,x) != ω.val (c,y) then (1:ℝ) else 0) ≤ dist x y/(4*r) := by
  rw [law,FiniteThreshold.threshold_separation (probability r) (probability_bounds r)]
  exact probability_lipschitz r hr c x y

end UniformKServer.HeavyRadius

end


end

end OAI
