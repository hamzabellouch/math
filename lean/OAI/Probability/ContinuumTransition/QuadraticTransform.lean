import OAI.Probability.ContinuumTransition.PressureRegularity

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

def shiftedField (a : ℝ) (x : Parameter) (d : ℝ) : Parameter :=
  (x.1,x.2+x.1*a*d)

def quadraticCost (Q : Parameter → ℝ) (a : ℝ) (x : Parameter) (d : ℝ) : ℝ :=
  Q (shiftedField a x d)-x.1*a*d^2/2

def IsMeanField (Q : Parameter → ℝ) (a : ℝ) (P : Parameter → ℝ) : Prop :=
  ∀ x ∈ pressureDomain, IsLUB (range (quadraticCost Q a x)) (P x)

noncomputable def meanField (Q : Parameter → ℝ) (a : ℝ) (x : Parameter) : ℝ :=
  sSup (range (quadraticCost Q a x))

lemma convolution_isLUB {Q H : ℝ → ℝ} {P β h a : ℝ} (hba : 0 ≤ β*a)
    (hQ : ∀ k, IsLUB ((fun d => k*d-H d) '' Ici 0) (Q k))
    (hP : IsLUB ((fun d => h*d+β*a*d^2/2-H d) '' Ici 0) P) :
    IsLUB (range (fun d => Q (h+β*a*d)-β*a*d^2/2)) P := by
  constructor
  · rintro _ ⟨d,rfl⟩
    have hu : Q (h+β*a*d) ≤ P+β*a*d^2/2 := by
      apply (hQ _).2
      rintro _ ⟨r,hr,rfl⟩
      have hh := hP.1 (mem_image_of_mem (fun r => h*r+β*a*r^2/2-H r) hr)
      have hs := mul_nonneg hba (sq_nonneg (r-d))
      nlinarith
    linarith
  · intro z hz
    apply hP.2
    rintro _ ⟨d,hd,rfl⟩
    have hh := (hQ (h+β*a*d)).1 (mem_image_of_mem (fun r => (h+β*a*d)*r-H r) hd)
    have hz' := hz (mem_range_self d)
    nlinarith

lemma isMeanField_meanField {Q P : Parameter → ℝ} {a : ℝ} (h : IsMeanField Q a P) :
    IsMeanField Q a (meanField Q a) := by
  intro x hx
  simpa only [meanField,(h x hx).csSup_eq (range_nonempty _)] using h x hx

lemma meanField_eq {Q P : Parameter → ℝ} {a : ℝ} (h : IsMeanField Q a P)
    {x : Parameter} (hx : x ∈ pressureDomain) : meanField Q a x = P x :=
  (h x hx).csSup_eq (range_nonempty _)

lemma meanField_convex {Q P : Parameter → ℝ} {a : ℝ}
    (hQ : ConvexOn ℝ pressureDomain Q) (hP : IsMeanField Q a P) :
    ConvexOn ℝ pressureDomain P := by
  refine ⟨hQ.1,?_⟩
  intro x hx y hy u v hu hv huv
  have hz := hQ.1 hx hy hu hv huv
  apply (hP _ hz).2
  rintro _ ⟨d,rfl⟩
  have hh := hQ.2 (show shiftedField a x d ∈ pressureDomain from hx)
    (show shiftedField a y d ∈ pressureDomain from hy) hu hv huv
  have he : u • shiftedField a x d+v • shiftedField a y d =
      shiftedField a (u • x+v • y) d := by ext <;> dsimp [shiftedField]; ring
  rw [he] at hh
  have h1 := mul_le_mul_of_nonneg_left ((hP x hx).1 (mem_range_self d)) hu
  have h2 := mul_le_mul_of_nonneg_left ((hP y hy).1 (mem_range_self d)) hv
  dsimp [quadraticCost] at *
  nlinarith only [hh,h1,h2]

lemma quadraticCost_continuous {Q : Parameter → ℝ} (hQ : ContinuousOn Q pressureDomain)
    {a : ℝ} {x : Parameter} (hx : x ∈ pressureDomain) :
    Continuous (quadraticCost Q a x) := by
  have hc : Continuous (fun d => Q (shiftedField a x d)) :=
    hQ.comp_continuous (by unfold shiftedField; fun_prop) (fun _ => hx)
  exact hc.sub (by fun_prop)

lemma maximizing_density_eq {Q P : Parameter → ℝ} {a : ℝ} (ha : 0 < a)
    (hP : IsMeanField Q a P) {x v : Parameter} (hx : x ∈ pressureDomain) {d : ℝ}
    (hd : quadraticCost Q a x d = P x)
    (hv : SupportOn pressureDomain Q (shiftedField a x d) v) : v.2 = d := by
  have hs := hv (shiftedField a x v.2) hx
  have hb := (hP x hx).1 (mem_range_self v.2)
  have hp : 0 < x.1*a := mul_pos hx ha
  dsimp [quadraticCost,shiftedField,pDot] at hd hs hb
  have he : x.1*a*(v.2-d)^2 ≤ 0 := by nlinarith only [hs,hb,hd]
  have hsq := nonpos_of_mul_nonpos_right he hp
  have hz := sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
  linarith

lemma lifted_support {Q P : Parameter → ℝ} {a : ℝ}
    (hP : IsMeanField Q a P) {x v : Parameter} (_hx : x ∈ pressureDomain) {d : ℝ}
    (hd : quadraticCost Q a x d = P x) (hvd : v.2 = d)
    (hv : SupportOn pressureDomain Q (shiftedField a x d) v) :
    SupportOn pressureDomain P x (v.1+a*d^2/2,d) := by
  intro y hy
  have hs := hv (shiftedField a y d) hy
  have hb := (hP y hy).1 (mem_range_self d)
  dsimp [quadraticCost,shiftedField,pDot] at *
  rw [hvd] at hs
  nlinarith only [hs,hb,hd]

end ContinuumTemperature
end
end

end OAI
