import Mathlib
import OAI.Combinatorics.Chromatic.Walls.PlanarJointFactorization
import OAI.Combinatorics.Chromatic.Walls.IsolatedPositivePlane

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit RootTruncation
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
omit [Algebra ℚ R] in
lemma chartZero_congr_through (h : M →+ ℝ) (F G : CompletedPositive v Ω C) (N : ℕ)
    (he : ∀n ≤ N,coeff n F.val=coeff n G.val) :
    ∀n ≤ N,coeff n (chartZero v Ω C h F).val=coeff n (chartZero v Ω C h G).val := by
  intro n hn
  exact zero_coeff_congr _ _ _ _ n (fun j hj => he j (hj.trans hn))
omit [Algebra ℚ R] in
lemma chart_sign_congr_through (h k : M →+ ℝ) (F : CompletedPositive v Ω C) (N : ℕ)
    (hs : ∀n,0 < n → n ≤ N → ∀m,HasRootDegree C n m →
      (0 < h m → 0 < k m) ∧ (h m=0 → k m=0) ∧ (h m < 0 → k m < 0)) :
    ∀n ≤ N,coeff n (chartZero v Ω C h F).val=coeff n (chartZero v Ω C k F).val := by
  have H:=chart_three_support v Ω C h F
  have HU:=chart_three_truncated_unique v Ω C k F
    (chartPositive v Ω C h F).val (chartZero v Ω C h F).val (chartNegative v Ω C h F).val N
    (chartPositive v Ω C h F).property.1 (chartZero v Ω C h F).property.1
    (chartNegative v Ω C h F).property.1 (chart_three_factorization v Ω C h F)
    (fun n hn m hm => (hs (n+1) (by omega) hn m
      (chart_root_of_ne v Ω C _ _ _ hm)).1 (H.1 n m hm))
    (fun n hn m hm => (hs (n+1) (by omega) hn m
      (chart_root_of_ne v Ω C _ _ _ hm)).2.1 (H.2.1 n m hm))
    (fun n hn m hm => (hs (n+1) (by omega) hn m
      (chart_root_of_ne v Ω C _ _ _ hm)).2.2 (H.2.2 n m hm))
  exact fun n hn => (HU n hn).2.1

def RayGeneric (N : ℕ) (r : M) (h : M →+ ℝ) : Prop :=
  h r=0 ∧ ∀n,0 < n → n ≤ N → ∀m,HasRootDegree C n m → h m=0 → OnPositiveRay r m
lemma RayGeneric.mono {N K : ℕ} {r : M} {h : M →+ ℝ}
    (H : RayGeneric C N r h) (hK : K ≤ N) : RayGeneric C K r h :=
  ⟨H.1,fun n hn hN m hm h0 => H.2 n hn (hN.trans hK) m hm h0⟩
omit [Algebra ℚ R] in
lemma RayGeneric.ray_supported {N : ℕ} {r : M} {h : M →+ ℝ}
    (H : RayGeneric C N r h) (F : CompletedPositive v Ω C) :
    ∀n,0 < n → n ≤ N → SupportedOn v Ω (OnPositiveRay r)
      (coeff n (chartZero v Ω C h F).val) := by
  intro n hn hN m hm
  by_contra hx
  have hr:=chart_root_of_ne v Ω C _ _ m hx
  cases n with
  | zero => omega
  | succ n => exact hm (H.2 (n+1) hn hN m hr ((chart_three_support v Ω C h F).2.1 n m hx))
end
section Closure
open PowerSeries RootTruncation
noncomputable section
variable {M : Type*} [AddCommGroup M]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
lemma RootClosedThrough.reduce {N K : ℕ} {A : Set (PowerSeries (Torus v Ω))}
    {F : PowerSeries (Torus v Ω)} (H : RootClosedThrough v Ω N A F) (hK : K ≤ N) :
    RootClosedThrough v Ω K A F := by
  intro T
  obtain ⟨G,hG,hagree⟩:=rootClosedThrough_approx_exists v Ω H T
  refine ⟨cut K G,⟨G,hG,rfl⟩,?_⟩
  intro t ht
  simp only [coeff_cut]
  by_cases hn : t.1 ≤ K
  · simp only [hn,ite_true]
    have Ht:=hagree t ht
    simpa only [coeff_cut,show t.1 ≤ N from hn.trans hK,ite_true] using Ht
  · simp only [hn,ite_false]; exact LaurentPrecision.agrees_refl _ _
end
end Closure
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit RootTruncation WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in
theorem positive_joint_transport (n dr : ℕ) (r : M) (s : E)
    (hdr : 0 < dr) (hrd : HasRootDegree C dr r) (hrs : B (e r) s≠0)
    (F : CompletedPositive LaurentRay.vUnit Ω C)
    (hF : ∀j,coeff j F.val∈supportedSubring LaurentRay.vUnit Ω (planeRoots e (e r) s))
    (hincoming : ∀p d,0 < d → d ≤ n+1 → HasRootDegree C d p → p∈planeRoots e (e r) s →
      RootClosedThrough LaurentRay.vUnit Ω (if Ω p r=0 then n+1 else n)
        (literalRootProducts Ω C (OnPositiveRay p))
        (chartZero LaurentRay.vUnit Ω C (incomingCovector Ω p) F).val) :
    RootClosedThrough LaurentRay.vUnit Ω (n+1) (literalRootProducts Ω C (OnPositiveRay r))
      (chartZero LaurentRay.vUnit Ω C (-incomingCovector Ω r) F).val := by
  classical
  have hr : 0 < L (e r):=by rw [hdeg dr r hrd]; exact_mod_cast hdr
  have hΩ : ∀m,Ω m m=0:=by
    intro m; have H:=hB (e m); rw [hcomp] at H; exact_mod_cast H
  obtain ⟨l,hl,hpair,hRay,hfact⟩:=planar_joint_factorization LaurentRay.vUnit Ω C e he B hB hcomp L hdeg
    (e r) s hr hrs F hF (n+1)
  let V:=planeRoots e (e r) s
  let h : M →+ ℝ:= -incomingCovector Ω r
  let Lm : M →+ ℝ:=L.toAddMonoidHom.comp e
  let J (p : M):=chartZero LaurentRay.vUnit Ω C (incomingCovector Ω p) F
  have hpP : ∀p∈l,e p∈Submodule.span ℝ {e r,s}:=by
    intro p hp; obtain ⟨d,hd,hdN,hdp,hpP⟩:=hl p hp; exact hpP
  have hpL : ∀p∈l,0 < Lm p:=by
    intro p hp; obtain ⟨d,hd,hdN,hdp,hpP⟩:=hl p hp
    change 0 < L (e p); rw [hdeg d p hdp]; exact_mod_cast hd
  have hplane : ∀p∈V,∀q∈V,(Ω p q:ℝ)=(-1/L (e r))*(h p*Lm q-Lm p*h q):=by
    intro p hp q hq
    have HH:=PlanarRayOrder.plane_determinant B hB L (e r) s (e p) (e q) hp hq
    simp only [hcomp] at HH
    change (Ω p q:ℝ)=(-1/L (e r))* (-(Ω p r:ℝ)*L (e q)-L (e p)* -(Ω q r:ℝ))
    field_simp [ne_of_gt hr]
    nlinarith only [HH]
  have H:=isolated_positive_plane Ω C hΩ Lm h V (-1/L (e r)) hplane n l
    (fun p => decide (Ω p r=0)) (fun p => OnPositiveRay p) J
    (fun p hp => by
      obtain ⟨d,hd,hdN,hdp,hpP⟩:=hl p hp
      simpa only [decide_eq_true_eq,J] using hincoming p d hd hdN hdp hpP)
    (fun p hp a b ha hb => ha.add hb)
    (fun p hp a ha => ⟨ha.mem_submodule e _ (hpP p hp), (ha.eval Lm).1.mpr (hpL p hp)⟩)
    (fun p hp a b ha hb => le_of_eq (ha.pair_zero Ω hb (hΩ p)).symm)
    (hpair.imp (fun {a b} hab p q hp hq => hp.pair_nonneg Ω hq hab.le))
    (fun p hp hact a ha => by
      have hn : Ω p r≠0:=by simpa only [decide_eq_false_iff_not] using hact
      intro hz
      have hz' : incomingCovector Ω r a=0:=by simpa only [h,AddMonoidHom.neg_apply,neg_eq_zero] using hz
      have hz'' := (ha.eval (incomingCovector Ω r)).2.1.mp hz'
      change (Ω p r:ℝ)=0 at hz''
      exact hn (by exact_mod_cast hz''))
    (fun p hp a ha => by
      by_contra hh
      exact ha (hRay p hp n (by omega) a hh))
  have Hn:=H.mono LaurentRay.vUnit Ω (literalRootProducts_allowed_mono Ω C _ (OnPositiveRay r) (by
    intro d hd p hp hpV
    have hz : B (e p) (e r)=0:=by
      rw [hcomp]
      have Hz:=hpV.2
      change -(Ω p r:ℝ)=0 at Hz
      exact neg_eq_zero.mp Hz
    exact positive_ray_of_pairing_zero e he B hB L (e r) s C hdeg hrs p r d dr hd hdr hp hrd
      hpV.1 (Submodule.subset_span (by simp)) hz))
  apply Hn.congr LaurentRay.vUnit Ω
  intro j hj
  exact zero_coeff_congr _ _ _ _ j (fun i hi => (hfact i (hi.trans hj)).symm)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
