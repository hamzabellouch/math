import OAI.Geometry.Convex.GeneralMahler.Compare
import OAI.Geometry.Convex.GeneralMahler.Packet

namespace OAI
/-! Layer functional ℒ and polynomial-growth calculus. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Interval
namespace GeneralMahler
open HMode Profile Layers

structure Bwt (l:Plane→ℝ) : Prop where
  c : Continuous l
  p : PolyBound l

def bInt (g:Plane→ℝ) (u:Plane) := ∫ y in u.1..u.2,g (u.1,y)
def bAv (g:Plane→ℝ) (u:Plane) := ∫ t in (0:ℝ)..1,g (u.1,along u t)

namespace Bwt
variable {l g:Plane→ℝ}
lemma add (h:Bwt l) (hh:Bwt g) : Bwt fun x=> l x+g x :=
  ⟨h.c.add hh.c,h.p.add hh.p⟩
lemma neg (h:Bwt l) : Bwt fun x=> -l x := ⟨h.c.neg,h.p.neg⟩
lemma sub (h:Bwt l) (hh:Bwt g) : Bwt fun x=> l x-g x :=
  ⟨h.c.sub hh.c,h.p.sub hh.p⟩
lemma mul (h:Bwt l) (hh:Bwt g) : Bwt fun x=> l x*g x :=
  ⟨h.c.mul hh.c,h.p.mul hh.p⟩
lemma fst {f:ℝ→ℝ} (hf:TestF f) : Bwt fun u:Plane=> f u.1 :=
  ⟨hf.cont.comp continuous_fst,hf.poly.comp PolyBound.fst⟩
lemma snd {f:ℝ→ℝ} (hf:TestF f) : Bwt fun u:Plane=> f u.2 :=
  ⟨hf.cont.comp continuous_snd,hf.poly.comp PolyBound.snd⟩
lemma const (c:ℝ) : Bwt fun _=>c := ⟨continuous_const,PolyBound.const _⟩
lemma bar (h:Bwt g) : Bwt (bAv g) := by
  constructor
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f:=fun (u:Plane) t=>g (u.1,along u t)) (h.c.comp (show Continuous (fun u:Plane×ℝ=>(u.1.1,along u.1 u.2)) by unfold along; fun_prop)) _ _
  obtain ⟨C,n,hc,h⟩ := h.p
  refine ⟨C,n,hc,fun u=>?_⟩
  have he (t:ℝ) (hh:t∈Ι (0:ℝ) 1) : ‖g (u.1,along u t)‖≤ C*(1+‖u‖)^n := by
    apply le_trans (h _)
    rw [uIoc_of_le zero_le_one] at hh
    gcongr;
    have ht := mem_Ioc.mp hh
    change max ‖u.1‖ ‖along u t‖ ≤ max _ _
    apply max_le (le_max_left ..)
    change |(1-t)*u.1+t*u.2| ≤ max |u.1| |u.2|
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul,abs_of_nonneg ht.1.le,abs_of_nonneg (by linarith [ht.2])]
    rcases max_choice |u.1| |u.2| with h|h
    · have hx := le_max_right |u.1| |u.2|
      rw [h] at *
      nlinarith [ht.1,ht.2]
    have hx := le_max_left |u.1| |u.2|
    rw [h] at *
    nlinarith [ht.1,ht.2]
  have hu := intervalIntegral.norm_integral_le_of_norm_le_const he
  unfold bAv; convert hu using 1 ; first | rfl | simp
lemma bar_eq (h:Bwt g) (u:Plane) :
    bInt g u=(u.2-u.1)*bAv g u := by
  let f := fun t=> ∫ z in u.1..t,g (u.1,z)
  have hf : Continuous (fun z=>g (u.1,z)) := h.c.comp (continuous_const.prodMk continuous_id)
  have hd (t:ℝ) : HasDerivAt f (g (u.1,t)) t := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable ..) (hf.stronglyMeasurableAtFilter volume _) hf.continuousAt
  have hi (t:ℝ) : HasDerivAt (f ∘ along u) (g (u.1,along u t)*(u.2-u.1)) t := by
    apply HasDerivAt.comp t (hd (along u t))
    convert ((((hasDerivAt_const t 1).sub (hasDerivAt_id' t)).mul_const u.1).fun_add
      ((hasDerivAt_id' t).mul_const u.2)) using 1
    all_goals first | rfl | ring
  have HH := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=> hi t)
    (((hf.comp (by unfold along; fun_prop)).mul continuous_const).intervalIntegrable (0:ℝ) 1)
  rw [intervalIntegral.integral_mul_const] at HH
  simp [along,f] at HH
  unfold bInt bAv; rw [mul_comm]
  convert HH.symm using 1 ; rfl
end Bwt
end GeneralMahler

end

end OAI
