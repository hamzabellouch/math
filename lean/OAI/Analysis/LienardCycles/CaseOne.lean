import OAI.Analysis.LienardCycles.CycleIsolation

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open ScaledProfile ScalarArcs AxisFlow RealAnalysis ScalarComparison
lemma linear_pos_open {a E F : ℝ → ℝ} {l r : ℝ} (hlr : l<r)
    (ha : ContinuousOn a (Icc l r)) (hE : ContinuousOn E (Icc l r))
    (hd : ∀ s ∈ Ioo l r,HasDerivAt E (-a s*E s+F s) s)
    (hF : ∀ s ∈ Ioo l r,0<F s) (h0 : 0≤E l) : 0<E r := by
  let ac : ℝ → ℝ := fun s=>a (projIcc l r hlr.le s)
  have hc : Continuous ac := (continuousOn_iff_continuous_domRestrict.mp ha).comp continuous_projIcc
  let w : ℝ → ℝ := fun s=>Real.exp (∫ u in l..s,ac u)
  have hw : Continuous w := continuous_iff_continuousAt.mpr fun s=>((hc.integral_hasStrictDerivAt l s).hasDerivAt.exp).continuousAt
  have hwd (s : ℝ) (hs : s ∈ Ioo l r) : HasDerivAt (fun s=>w s*E s) (w s*F s) s := by
    have H := ((hc.integral_hasStrictDerivAt l s).hasDerivAt.exp).mul (hd s hs)
    have he : ac s=a s := by simp only [ac,projIcc_of_mem hlr.le (Ioo_subset_Icc_self hs)]
    rw [he] at H
    convert! H using 1
    dsimp only [w]
    ring
  have hm : StrictMonoOn (fun s=>w s*E s) (Icc l r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (hw.continuousOn.mul hE)
    intro s hs
    have hs' : s ∈ Ioo l r := by simpa using hs
    change 0<deriv (fun s=>w s*E s) s
    rw [(hwd s hs').deriv]
    exact mul_pos (Real.exp_pos _) (hF s hs')
  have hp := hm ⟨le_rfl,hlr.le⟩ ⟨hlr.le,le_rfl⟩ hlr
  have hw0 : w l=1 := by simp [w]
  dsimp only at hp
  rw [hw0,one_mul] at hp
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp (h0.trans_lt hp)
noncomputable def oddPart (a : Fin 6 → ℝ) (u : ℝ) : ℝ := a 1*root u+a 3*(root u)^3+a 5*(root u)^5
lemma oddPart_pos {a : Fin 6 → ℝ} (h1 : 0≤a 1) (h3 : 0≤a 3) (h5 : 0≤a 5)
    (hne : a 1≠0 ∨ a 3≠0 ∨ a 5≠0) {u : ℝ} (hu : 0<u) : 0<oddPart a u := by
  have hr := root_pos hu
  have hA := mul_nonneg h1 hr.le
  have hB := mul_nonneg h3 (pow_nonneg hr.le 3)
  have hC := mul_nonneg h5 (pow_nonneg hr.le 5)
  rcases hne with h|h|h
  · have H := mul_pos (lt_of_le_of_ne h1 h.symm) hr
    dsimp [oddPart];linarith
  · have H := mul_pos (lt_of_le_of_ne h3 h.symm) (pow_pos hr 3)
    dsimp [oddPart];linarith
  · have H := mul_pos (lt_of_le_of_ne h5 h.symm) (pow_pos hr 5)
    dsimp [oddPart];linarith
lemma profile_odd_difference (a : Fin 6 → ℝ) {u v : ℝ} (hu : 0≤u) (hv : 0≤v) :
    φ a u-φ (reflectX a) v=(2*a 2+4*a 4*(u+v))*(u-v)+oddPart a u+oddPart a v := by
  have hu4 : (root u)^4=4*u^2 := by calc
    _=((root u)^2)^2 := by ring
    _=4*u^2 := by rw [root_sq hu];ring
  have hv4 : (root v)^4=4*v^2 := by calc
    _=((root v)^2)^2 := by ring
    _=4*v^2 := by rw [root_sq hv];ring
  rw [φ,φ,reflectX_poly]
  have hn (x : ℝ) : poly a (-x)=a 0-a 1*x+a 2*x^2-a 3*x^3+a 4*x^4-a 5*x^5 := by dsimp [poly];ring
  rw [hn]
  dsimp [poly,oddPart]
  rw [root_sq hu,root_sq hv,hu4,hv4]
  ring
lemma no_periodic_case1 {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) (h1 : 0≤a 1) (h3 : 0≤a 3) (h5 : 0≤a 5)
    (hne : a 1≠0 ∨ a 3≠0 ∨ a 5≠0) {C : Set Plane} : ¬IsPeriodicOrbit F C := by
  intro hC
  obtain ⟨z,S,T,hz,_,_,hp,hr,hl,_⟩ := hC.oval hF
  have hzT : z T=z 0 := by simpa using hp 0
  obtain ⟨u,hu,huA,huB,hud,_⟩ := hr.graph hF hz
  obtain ⟨v,hv,hvA,hvB,hvd,_⟩ := hl.graph (a:=reflectX a)
    (fun x=>by rw [polynomialReflect_eval,hF,reflectX_poly]) hz.reverseX
  simp only [QuinticLienard.reverseX,neg_neg,hzT] at hvA hvB hvd
  have hpos := linear_pos_open (a:=fun y=>-(2*a 2+4*a 4*(u y+v y)))
    (E:=fun y=>u y-v y) (F:=fun y=>oddPart a (u y)+oddPart a (v y)) (hr.y_lt hz)
    (by fun_prop) (hu.sub hv).continuousOn
    (fun y hy=>by
      convert! (hud y hy).2.sub (hvd y hy).2 using 1
      rw [show (φ a (u y)-y)-(φ (reflectX a) (v y)-y)=φ a (u y)-φ (reflectX a) (v y) by ring]
      rw [profile_odd_difference a (hud y hy).1.le (hvd y hy).1.le]
      ring)
    (fun y hy=>add_pos (oddPart_pos h1 h3 h5 hne (hud y hy).1) (oddPart_pos h1 h3 h5 hne (hvd y hy).1))
    (by rw [huA,hvA,sub_self])
  rw [huB,hvB,sub_self] at hpos
  exact lt_irrefl _ hpos
end QuinticLienard

end OAI
