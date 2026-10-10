import OAI.Geometry.Convex.GeneralMahler.Eq14

namespace OAI
/-! Scalar primitive conventions and calculus for §04. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.Profile
open Layers
def prim (l:ℝ→ℝ) (x:ℝ) := ∫ t in (0:ℝ)..x,l t
lemma prim_d {l} (hf:TestF l) (x) : HasDerivAt (prim l) (l x) x :=
  intervalIntegral.integral_hasDerivAt_right (hf.cont.intervalIntegrable ..)
    (hf.cont.stronglyMeasurableAtFilter volume _) hf.cont.continuousAt
lemma p_test {l} (hf:TestF l) : TestF (prim l) := TestF.of_d (prim_d hf) hf

def pl (l:ℝ→ℝ) (x) := prim l x-ga (prim l)
lemma pl_test {l} (hf:TestF l) : TestF (pl l) :=
  (p_test hf).sub (TestF.const _)
lemma pl_d {l} (hf:TestF l) : deriv (pl l)=l :=
  funext fun x=> ((prim_d hf x).sub_const (ga (prim l))).deriv
lemma ga_const (c:ℝ) : ga (fun _=>c)=c := by unfold ga; rw [integral_mul_const,e_phi]; ring
lemma pl_ga {l} (hl:TestF l) : ga (pl l)=0 := by
  rw [show ga (pl l)=_ from ga_sub (p_test hl) (TestF.const _),ga_const,sub_self]

def fl (l:ℝ→ℝ) := Nr (pl l)
def ps (l:ℝ→ℝ) := prim fun x=> N (pl l) x-pl l x
lemma N_test {l} (hl:TestF l) : TestF (N l) :=
  (TestF.id.mul hl.der).sub hl.der.der
lemma fl_test {l} (hl:TestF l) : TestF (fl l) := nr_test (pl_test hl)
lemma ps_test {l} (hl:TestF l) : TestF (ps l) :=
  p_test ((N_test (pl_test hl)).sub (pl_test hl))
lemma fl_d {l} (hl:TestF l) : deriv (fl l)=N2 l := by
  unfold fl Nr N
  rw [pl_d hl]
  ext x
  have he := (((pl_test hl).diff x).hasDerivAt.fun_add (((hasDerivAt_id' x).fun_mul
    (hl.diff x).hasDerivAt).fun_sub (hl.der.diff x).hasDerivAt)).deriv
  simp only [pl_d hl] at he
  unfold N2 N; rw [he]; ring
lemma ps_d {l} (hl:TestF l) (x) : deriv (ps l) x=fl l x-2*pl l x := by
  rw [show deriv (ps l) x=_ from (prim_d ((N_test (pl_test hl)).sub (pl_test hl)) x).deriv]
  unfold fl Nr; ring
lemma Nr_ga {b} (hb:TestF b) : ga (Nr b)=ga b := by
  unfold Nr
  rw [ga_add hb (N_test hb)]; unfold N
  rw [ga_sub (TestF.id.mul hb.der) hb.der.der,
    ga_parts hb.der]; ring
lemma fl_ga {l} (hl:TestF l) : ga (fl l)=0 := (Nr_ga (pl_test hl)).trans (pl_ga hl)

lemma ga_N_parts {f g} (hf:TestF f) (hg:TestF g) :
    ga (fun x=> N f x*g x) = ga (fun x=>deriv f x*deriv g x) := ga_pair hf.der hg
lemma ga_nr_parts {f g} (hf:TestF f) (hg:TestF g) :
    ga (fun x=> Nr f x*g x)=ga (fun x=>f x*g x)+ga (fun x=>deriv f x*deriv g x) := by
  unfold Nr; simp_rw [add_mul]
  rw [ga_add (hf.mul hg) ((N_test hf).mul hg),ga_N_parts hf hg]
lemma id_ga : ga (fun x=>x)=0 := by
  simpa [ga] using ga_parts (TestF.const 1)
end GeneralMahler.Profile

end

end OAI
