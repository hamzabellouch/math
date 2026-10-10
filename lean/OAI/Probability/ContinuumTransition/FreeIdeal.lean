import OAI.Probability.ContinuumTransition.PhysicalUniform

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def threeCore (p : ℝ) (x : Parameter) : ℝ := max 0 (max (p*x.2) (4*p*x.2-9*p))
def threeMeanField (p a : ℝ) (x : Parameter) : ℝ :=
  max 0 (max (p*x.2+x.1*a*p^2/2) (4*p*x.2-9*p+x.1*a*(4*p)^2/2))
def firstMass (p : ℝ) : ℝ := 3/(2*p)
def initialPoint : Parameter := (1,-3/4)

lemma threeCore_convex (p : ℝ) : ConvexOn ℝ pressureDomain (threeCore p) := by
  have hdom : Convex ℝ pressureDomain := by
    change Convex ℝ {x : Parameter | 0 < x.1}
    exact (convex_Ioi (0 : ℝ)).linear_preimage (LinearMap.fst ℝ ℝ ℝ)
  apply (convexOn_const (0 : ℝ) hdom).sup
  apply ConvexOn.sup
  · refine ⟨hdom,?_⟩
    intro x hx y hy a b ha hb hab
    dsimp
    nlinarith
  · refine ⟨hdom,?_⟩
    intro x hx y hy a b ha hb hab
    dsimp
    have hh := congrArg (fun z : ℝ => z*(9*p)) hab
    nlinarith only [hh]

lemma three_meanField {p a : ℝ} (ha : 0 ≤ a) : IsMeanField (threeCore p) a (threeMeanField p a) := by
  intro x hx
  have hcoef : 0 ≤ x.1*a := mul_nonneg (le_of_lt hx) ha
  have h0 : ∀ d : ℝ, -(x.1*a*d^2/2) ≤ 0 := fun d => neg_nonpos.mpr (div_nonneg (mul_nonneg hcoef (sq_nonneg d)) (by norm_num))
  have h1 : ∀ d : ℝ, p*(x.2+x.1*a*d)-x.1*a*d^2/2 ≤ p*x.2+x.1*a*p^2/2 := by
    intro d
    have hh := mul_nonneg hcoef (sq_nonneg (d-p))
    nlinarith only [hh]
  have h2 : ∀ d : ℝ, 4*p*(x.2+x.1*a*d)-9*p-x.1*a*d^2/2 ≤ 4*p*x.2-9*p+x.1*a*(4*p)^2/2 := by
    intro d
    have hh := mul_nonneg hcoef (sq_nonneg (d-4*p))
    nlinarith only [hh]
  constructor
  · rintro _ ⟨d,rfl⟩
    change max 0 (max (p*(x.2+x.1*a*d)) (4*p*(x.2+x.1*a*d)-9*p))-x.1*a*d^2/2 ≤ _
    rw [← max_sub_sub_right,← max_sub_sub_right]
    apply max_le
    · exact (show 0-x.1*a*d^2/2 ≤ 0 by simpa using h0 d).trans (le_max_left _ _)
    · apply max_le
      · exact (h1 d).trans ((le_max_left _ _).trans (le_max_right _ _))
      · exact (h2 d).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro b hb
    have he0 := hb (mem_range_self (0:ℝ))
    have he1 := hb (mem_range_self p)
    have he2 := hb (mem_range_self (4*p))
    have hl0 : 0 ≤ quadraticCost (threeCore p) a x 0 := by
      simp only [quadraticCost,shiftedField,mul_zero,add_zero,zero_pow (by decide : 2 ≠ 0),zero_div,sub_zero,threeCore]
      exact le_max_left _ _
    have hl1 : p*x.2+x.1*a*p^2/2 ≤ quadraticCost (threeCore p) a x p := by
      have hh := (le_max_left (p*(x.2+x.1*a*p)) (4*p*(x.2+x.1*a*p)-9*p)).trans (le_max_right (0:ℝ) _)
      dsimp [quadraticCost,shiftedField,threeCore]
      nlinarith only [hh]
    have hl2 : 4*p*x.2-9*p+x.1*a*(4*p)^2/2 ≤ quadraticCost (threeCore p) a x (4*p) := by
      have hh := (le_max_right (p*(x.2+x.1*a*(4*p))) (4*p*(x.2+x.1*a*(4*p))-9*p)).trans (le_max_right (0:ℝ) _)
      dsimp [quadraticCost,shiftedField,threeCore]
      nlinarith only [hh]
    exact max_le (hl0.trans he0) (max_le (hl1.trans he1) (hl2.trans he2))

lemma support_first_zero {f : ℝ → ℝ} {x w : Parameter} (hx : x ∈ pressureDomain)
    (hw : SupportOn pressureDomain (fun y => f y.2) x w) : w.1=0 := by
  change 0 < x.1 at hx
  have h1 := hw (2*x.1,x.2) (by change 0 < 2*x.1; positivity)
  have h2 := hw (x.1/2,x.2) (by change 0 < x.1/2; positivity)
  dsimp [pDot] at h1 h2
  nlinarith [hx]

lemma firstMass_pos {p : ℝ} (hp : 0 < p) : 0 < firstMass p := by unfold firstMass; positivity
lemma firstMass_mul {p : ℝ} (hp : 0 < p) : firstMass p*p = 3/2 := by
  unfold firstMass
  field_simp

lemma threeMeanField_initial {p : ℝ} (hp : 0 < p) : threeMeanField p (firstMass p) initialPoint=0 := by
  have hh := firstMass_mul hp
  have hh2 : firstMass p*p^2=3*p/2 := by linear_combination p*hh
  have h1 : p*(-3/4)+firstMass p*p^2/2=0 := by nlinarith only [hh2]
  have h2 : 4*p*(-3/4)-9*p+firstMass p*(4*p)^2/2=0 := by nlinarith only [hh2]
  simp only [threeMeanField,initialPoint,one_mul,h1,h2,max_self]

lemma three_active_initial {p : ℝ} (hp : 0 < p) :
    activeLifts (threeCore p) (firstMass p) (threeMeanField p (firstMass p)) initialPoint ⊆ range (triangleVertex p) := by
  intro w hw
  have hβ : initialPoint ∈ pressureDomain := by norm_num [initialPoint,pressureDomain]
  have he := support_first_zero (f := fun h => max 0 (max (p*h) (4*p*h-9*p))) (show shiftedField (firstMass p) initialPoint w.2 ∈ pressureDomain from hβ) hw.2
  have hc := hw.1
  rw [threeMeanField_initial hp] at hc
  have ha := firstMass_pos hp
  have hap := firstMass_mul hp
  have hap2 : firstMass p*p^2=3*p/2 := by linear_combination p*hap
  have hapd : firstMass p*p*w.2=3*w.2/2 := by linear_combination w.2*hap
  change w.1-firstMass p*w.2^2/2=0 at he
  simp only [quadraticCost,threeCore,shiftedField,initialPoint,one_mul] at hc
  change max 0 (max (p*(-3/4+firstMass p*w.2)) (4*p*(-3/4+firstMass p*w.2)-9*p))-firstMass p*w.2^2/2=0 at hc
  rcases le_total 0 (max (p*(-3/4+firstMass p*w.2)) (4*p*(-3/4+firstMass p*w.2)-9*p)) with h | h
  · rw [max_eq_right h] at hc
    rcases le_total (p*(-3/4+firstMass p*w.2)) (4*p*(-3/4+firstMass p*w.2)-9*p) with hh | hh
    · rw [max_eq_right hh] at hc
      have hd : w.2=4*p := by
        have hh1 : firstMass p*(w.2-4*p)^2=0 := by nlinarith only [hc,hap2,hapd]
        have := (mul_eq_zero.mp hh1).resolve_left ha.ne'
        nlinarith [sq_nonneg (w.2-4*p)]
      refine ⟨2,?_⟩
      ext <;> norm_num [triangleVertex,show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide]
      · rw [hd] at he; nlinarith only [he,hap2]
      · exact hd.symm
    · rw [max_eq_left hh] at hc
      have hd : w.2=p := by
        have hh1 : firstMass p*(w.2-p)^2=0 := by nlinarith only [hc,hap2,hapd]
        have := (mul_eq_zero.mp hh1).resolve_left ha.ne'
        nlinarith [sq_nonneg (w.2-p)]
      refine ⟨1,?_⟩
      ext <;> norm_num [triangleVertex]
      · rw [hd] at he; nlinarith only [he,hap2]
      · exact hd.symm
  · rw [max_eq_left h] at hc
    have hd : w.2=0 := by
      have hm : firstMass p*w.2^2=0 := by linarith only [hc]
      have hs := (mul_eq_zero.mp hm).resolve_left ha.ne'
      nlinarith [sq_nonneg w.2]
    refine ⟨0,?_⟩
    ext <;> norm_num [triangleVertex]
    · rw [hd] at he; simpa using he.symm
    · exact hd.symm

end ContinuumTemperature
end
end

end OAI
