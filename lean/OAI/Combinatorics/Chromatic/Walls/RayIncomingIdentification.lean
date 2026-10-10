import Mathlib
import OAI.Combinatorics.Chromatic.Walls.IncomingDisplacement
import OAI.Combinatorics.Chromatic.Walls.PlanarRayOrder

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A] [Module ℚ A]
lemma log_injective_through (F G : PowerSeries A) (N : ℕ)
    (hF : constantCoeff F=1) (hG : constantCoeff G=1)
    (h : ∀n≤N,coeff n (log F)=coeff n (log G)) :
    ∀n≤N,coeff n F=coeff n G := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp only [coeff_zero_eq_constantCoeff,hF,hG]
    | succ n =>
      have H:=log_leading_difference F G n hF hG
        (fun j hj=>ih j (by omega) (by omega))
      rw [h (n+1) hn,sub_self] at H
      exact sub_eq_zero.mp H.symm
lemma log_injective (F G : PowerSeries A) (hF : constantCoeff F=1)
    (hG : constantCoeff G=1) (h : log F=log G) : F=G := by
  ext n
  exact log_injective_through F G n hF hG (fun j _=>congrArg (coeff j) h) n le_rfl
end
end ElementaryPositivity.FormalLog

namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

def OnPositiveRay (r m : M) : Prop := ∃a b : ℕ,0<a ∧ 0<b ∧ a • m=b • r

lemma OnPositiveRay.refl (r : M) : OnPositiveRay r r := ⟨1,1,one_pos,one_pos,by simp⟩
lemma OnPositiveRay.eval {r m : M} (hm : OnPositiveRay r m) (h : M→+ℝ) :
    (0<h m↔0<h r) ∧ (h m=0↔h r=0) ∧ (h m<0↔h r<0) := by
  obtain ⟨a,b,ha,hb,he⟩:=hm
  have H:=congrArg h he
  simp only [map_nsmul,nsmul_eq_mul] at H
  have ha' : (0:ℝ)<a:=by exact_mod_cast ha
  have hb' : (0:ℝ)<b:=by exact_mod_cast hb
  constructor
  · constructor <;> intro h <;> nlinarith
  constructor <;> constructor <;> intro h <;> nlinarith

lemma OnPositiveRay.incomingSigns {r m : M} (hm : OnPositiveRay r m) (x : M) :
    (0 < incomingCovector Ω r x↔0 < incomingCovector Ω m x) ∧
    (incomingCovector Ω r x=0↔incomingCovector Ω m x=0) ∧
    (incomingCovector Ω r x<0↔incomingCovector Ω m x<0) := by
  let h : M→+ℝ := (Int.castAddHom ℝ).comp (Ω x)
  have H:=hm.eval h
  exact ⟨H.1.symm,H.2.1.symm,H.2.2.symm⟩

omit [Algebra ℚ R] in
lemma chart_sign_congr (h k : M→+ℝ) (F : CompletedPositive v Ω C)
    (H : ∀m,(0<h m↔0<k m) ∧ (h m=0↔k m=0) ∧ (h m<0↔k m<0)) :
    chartPositive v Ω C h F=chartPositive v Ω C k F ∧
    chartZero v Ω C h F=chartZero v Ω C k F ∧
    chartNegative v Ω C h F=chartNegative v Ω C k F := by
  have hs:=chart_three_support v Ω C h F
  exact chart_three_unique v Ω C k F _ _ _ (chart_three_factorization v Ω C h F)
    (fun n m hm=>(H m).1.mp (hs.1 n m hm))
    (fun n m hm=>(H m).2.1.mp (hs.2.1 n m hm))
    (fun n m hm=>(H m).2.2.mp (hs.2.2 n m hm))

omit [Algebra ℚ R] in
lemma incoming_same_ray {r m : M} (hm : OnPositiveRay r m) (F : CompletedPositive v Ω C) :
    chartZero v Ω C (incomingCovector Ω r) F=chartZero v Ω C (incomingCovector Ω m) F :=
  (chart_sign_congr v Ω C _ _ F (hm.incomingSigns Ω)).2.1

theorem incoming_ray_log (hΩ : ∀m,Ω m m=0) (r : M) (k : M→+ℝ) (hk : k r=0)
    (F : CompletedPositive v Ω C) (m : M) (hm : OnPositiveRay r m) (n : ℕ) :
    coeff n (FormalLog.log (chartZero v Ω C k
      (chartZero v Ω C (incomingCovector Ω r) F)).val) m=
    coeff n (FormalLog.log (chartZero v Ω C (incomingCovector Ω m) F).val) m := by
  rw [incoming_same_ray v Ω C hm F]
  exact incoming_displacement_log v Ω C hΩ m k ((hm.eval k).2.1.mpr hk) F n

end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (e : M→+E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (L : Module.Dual ℝ E) (r s : E)

include he hB in
lemma positive_ray_of_pairing_zero (C : (I→ℤ)→+M)
    (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
    (hrs : B r s≠0) (m p : M) (n d : ℕ) (hn : 0<n) (hd : 0<d)
    (hm : HasRootDegree C n m) (hp : HasRootDegree C d p)
    (hmP : e m∈Submodule.span ℝ {r,s}) (hpP : e p∈Submodule.span ℝ {r,s})
    (hmp : B (e m) (e p)=0) : OnPositiveRay p m := by
  refine ⟨d,n,hd,hn,he ?_⟩
  have H:=PlanarRayOrder.plane_normalized_eq B hB L r s (e m) (e p) hrs hmP hpP hmp
  simpa only [hdeg n m hm,hdeg d p hp,Nat.cast_smul_eq_nsmul,map_nsmul] using H

include hB in

lemma finite_positive_ray_order (S : Finset M) (hr : 0<L r)
    (hS : ∀m∈S,0<L (e m) ∧ e m∈Submodule.span ℝ {r,s}) :
    ∃l : List M,(∀p∈l,p∈S) ∧ l.Pairwise (fun a b => 0<B (e a) (e b)) ∧
      ∀m∈S,∃p∈l,B (e m) (e p)=0 := by
  classical
  let slope : M → ℝ:=fun m => PlanarRayOrder.slope B L r (e m)
  let T:=S.image slope
  have hchoose (a : ℝ) (ha : a∈T) : ∃m∈S,slope m=a:=Finset.mem_image.mp ha
  let c (a : ℝ) : M:=if ha : a∈T then Classical.choose (hchoose a ha) else 0
  have hc : ∀a∈T,c a∈S ∧ slope (c a)=a:=by
    intro a ha
    dsimp [c]
    rw [dite_eq_left ha]
    exact Classical.choose_spec (hchoose a ha)
  let ts:=T.sort (· ≥ ·)
  have hts : ts.Pairwise (fun a b => b<a):=(T.sortedGT_sort).pairwise
  have hmem : ∀a∈ts,a∈T:=fun a ha => (Finset.mem_sort _).mp ha
  refine ⟨ts.map c,?_,?_,?_⟩
  · intro p hp
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hp
    exact (hc a (hmem a ha)).1
  · rw [List.pairwise_map]
    apply hts.imp_of_mem
    intro a b ha hb hab
    have hca:=hc a (hmem a ha)
    have hcb:=hc b (hmem b hb)
    apply (PlanarRayOrder.pairing_pos_iff B hB L r s (e (c a)) (e (c b)) hr
      (hS _ hca.1).1 (hS _ hcb.1).1 (hS _ hca.1).2 (hS _ hcb.1).2).mpr
    change slope (c b)<slope (c a)
    rw [hca.2,hcb.2]
    exact hab
  · intro m hm
    have ht : slope m∈T:=Finset.mem_image.mpr ⟨m,hm,rfl⟩
    have hh:=hc (slope m) ht
    refine ⟨c (slope m),List.mem_map.mpr ⟨slope m,(Finset.mem_sort _).mpr ht,rfl⟩,?_⟩
    apply (PlanarRayOrder.pairing_zero_iff B hB L r s (e m) (e (c (slope m))) hr
      (hS _ hm).1 (hS _ hh.1).1 (hS _ hm).2 (hS _ hh.1).2).mpr
    exact hh.2
end
end ElementaryPositivity.QuantumTorus

end

end OAI
