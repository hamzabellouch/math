import Mathlib
import OAI.Combinatorics.Chromatic.Walls.GlobalWallPositive
import OAI.Combinatorics.Chromatic.Walls.GeometricFinitePositive
import OAI.Combinatorics.Chromatic.GradedAlgebra.CovectorFactor

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open RawShuffle SlopeArithmetic WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {M J : Type*} [AddCommGroup M] [Fintype J]
variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M) (V : AddSubmonoid M)
variable (hΩ : ∀p,Ω p p=0) (hV : ∀p∈V,∀q∈V,Ω p q=0)
include hΩ hV in
lemma literal_isotropic_adjoint {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : F∈literalRootProducts Ω C (fun p=>p∈V)) :
    (∀m,(∀p∈V,0≤Ω p m)→IntegralPositive Ω
      (F*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1)) ∧
    (∀m,(∀p∈V,Ω p m≤0)→IntegralPositive Ω
      (invOfUnit F 1*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*F)) := by
  classical
  have hconstant:=literalRootProducts_constant Ω C (fun p=>p∈V) hF
  obtain ⟨l,hl,rfl⟩:=hF
  let p : Fin l.length→M:=fun i=>(l.get i).root
  let w : Fin l.length→ℕ:=fun i=>(l.get i).degree
  let c : Fin l.length→ℝ:=fun i=>w i
  let κ : Fin l.length→ℤ:=fun i=>(l.get i).parameter
  let ε : Fin l.length→Bool:=fun i=>decide ((l.get i).kind=0)
  have hall : ∀i,(l.get i).Allowed C (fun p=>p∈V):=fun i=>hl _ (List.get_mem _ _)
  let : Fact (∀i,0<w i):=⟨fun i=>(hall i).1⟩
  have hc : ∀i,0<c i:=fun i=>by
    change 0<((l.get i).degree:ℝ)
    exact_mod_cast (hall i).1
  have hp : ∀i j,(Ω (p i) (p j):ℝ)=(0:ℝ)*((0:ℝ)*c j-c i*0):=by
    intro i j
    rw [hV _ (hall i).2.2 _ (hall j).2.2]
    simp
  have ho : (List.finRange l.length).Pairwise (fun i j=>0≤Ω (p i) (p j)):=by
    apply List.pairwise_of_forall
    intro i j
    rw [hV _ (hall i).2.2 _ (hall j).2.2]
  have hh : ∀d,(0 : M→+ℝ) (rootSum p d)=slopeValue c (fun _=>0) 0 d:=by
    intro d
    simp [slopeValue,mass]
  have Hprod:=listLiteral_product Ω l
  change ((List.finRange l.length).map (literalAxis κ ε Ω (rootSum p) w)).prod=_ at Hprod
  have Hzero : PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω (0:M→+ℝ))
      (zeroProject LaurentRay.vUnit Ω (0:M→+ℝ))
      (((List.finRange l.length).map (literalAxis κ ε Ω (rootSum p) w)).prod)=
      (l.map (WallUnitDatum.value Ω)).prod := by
    rw [Hprod,zeroFactor_zero _ _ _ hconstant]
  constructor
  · intro m hm
    have H:=geometric_zero_adjoint_positive Ω hΩ p κ ε w c (fun _=>0) hc 0 hp
      (List.finRange l.length) (List.nodup_finRange _) (List.toFinset_finRange _) ho
      (0:M→+ℝ) 0 hh m (fun d hd=>hm _ (rootSum_mem p V (fun i=>(hall i).2.2) d))
    dsimp only at H
    rwa [Hzero] at H
  · intro m hm
    have H:=geometric_zero_inverse_adjoint_positive Ω hΩ p κ ε w c (fun _=>0) hc 0 hp
      (List.finRange l.length) (List.nodup_finRange _) (List.toFinset_finRange _) ho
      (0:M→+ℝ) 0 hh m (fun d hd=>hm _ (rootSum_mem p V (fun i=>(hall i).2.2) d))
    dsimp only at H
    rwa [Hzero] at H
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision Filter WallUnits
noncomputable section
variable {M J ι : Type*} [AddCommGroup M] [Fintype J]
variable (Ω : M→+M→+ℤ) (C : (J→ℤ)→+M) (l : Filter ι)
lemma SeriesConverges.inverse_adjoint
    {f : ι→PowerSeries (Torus LaurentRay.vUnit Ω)} {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hf : SeriesConverges LaurentRay.vUnit Ω l f F)
    (hfg : ∀i,SeriesGraded LaurentRay.vUnit Ω C (f i))
    (hF : SeriesGraded LaurentRay.vUnit Ω C F) (x : Torus LaurentRay.vUnit Ω) :
    SeriesConverges LaurentRay.vUnit Ω l (fun i=>invOfUnit (f i) 1*PowerSeries.C x*f i)
      (invOfUnit F 1*PowerSeries.C x*F) := by
  have H:=hf.inverse LaurentRay.vUnit Ω C l hfg hF
  have hi : ∀i,SeriesGraded LaurentRay.vUnit Ω C (invOfUnit (f i) 1):=
    fun i=>(hfg i).inverse LaurentRay.vUnit Ω C
  have hI:=hF.inverse LaurentRay.vUnit Ω C
  exact (H.mul_C LaurentRay.vUnit Ω C l hi hI x).mul_of_support LaurentRay.vUnit Ω l hf
    (fun n=>sumSupport (rootDegree_finite C n).toFinset x.support)
    (fun n=>(rootDegree_finite C n).toFinset)
    (fun i n=>(hi i).mul_C_support LaurentRay.vUnit Ω C x n)
    (fun i n=>rootGrade_support LaurentRay.vUnit Ω C n _ (hfg i n))
    (fun n=>hI.mul_C_support LaurentRay.vUnit Ω C x n)
    (fun n=>rootGrade_support LaurentRay.vUnit Ω C n _ (hF n))

variable (V : AddSubmonoid M) (hΩ : ∀p,Ω p p=0) (hV : ∀p∈V,∀q∈V,Ω p q=0)
include hΩ hV in

theorem closed_isotropic_adjoint {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C (fun p=>p∈V)) F) :
    (∀m,(∀p∈V,0≤Ω p m)→IntegralPositive Ω
      (F*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1)) ∧
    (∀m,(∀p∈V,Ω p m≤0)→IntegralPositive Ω
      (invOfUnit F 1*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*F)) := by
  let f:=precisionApprox LaurentRay.vUnit Ω hF
  have hf:=precisionApprox_converges LaurentRay.vUnit Ω hF
  have hg : ∀T,SeriesGraded LaurentRay.vUnit Ω C (f T):=fun T=>
    literalRootProducts_graded Ω C (fun p=>p∈V) (precisionApprox_mem LaurentRay.vUnit Ω hF T)
  have hFG:=hF.graded Ω C (fun G hG=>literalRootProducts_graded Ω C (fun p=>p∈V) hG)
  have hpositive : ∀T,
      (∀m,(∀p∈V,0≤Ω p m)→IntegralPositive Ω
        (f T*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit (f T) 1)) ∧
      (∀m,(∀p∈V,Ω p m≤0)→IntegralPositive Ω
        (invOfUnit (f T) 1*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*f T)):=fun T=>
    literal_isotropic_adjoint Ω C V hΩ hV (precisionApprox_mem LaurentRay.vUnit Ω hF T)
  constructor
  · intro m hm
    exact IntegralPositive.of_converges Ω Filter.atTop
      (hf.adjoint LaurentRay.vUnit Ω C Filter.atTop hg hFG _)
      (Eventually.of_forall (fun T=>(hpositive T).1 m hm))
  · intro m hm
    exact IntegralPositive.of_converges Ω Filter.atTop
      (hf.inverse_adjoint Ω C Filter.atTop hg hFG _)
      (Eventually.of_forall (fun T=>(hpositive T).2 m hm))
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits LaurentPrecision
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
lemma inPrecisionClosure_of_cuts (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
    (A : Set (PowerSeries (Torus v Ω))) (F : PowerSeries (Torus v Ω))
    (hF : ∀N,RootClosedThrough v Ω N A F) : InPrecisionClosure v Ω A F := by
  classical
  intro T
  let N:=T.sup (fun t=>t.1)
  obtain ⟨G,hG,H⟩:=rootClosedThrough_approx_exists v Ω (hF N) T
  refine ⟨G,hG,?_⟩
  intro t ht
  have hn : t.1≤N:=Finset.le_sup (f:=fun t : PrecisionTest (M:=M)=>t.1) ht
  have hh:=H t ht
  simpa only [RootTruncation.coeff_cut,ite_eq_left hn] using hh

def positiveRayWithZero (r : M) : AddSubmonoid M where
  carrier:={m | m=0 ∨ OnPositiveRay r m}
  zero_mem':=Or.inl rfl
  add_mem':=by
    intro a b ha hb
    rcases ha with rfl|ha
    · simpa using hb
    rcases hb with rfl|hb
    · simpa using Or.inr ha
    · exact Or.inr (ha.add hb)
variable (Ω : M →+ M →+ ℤ)
lemma positiveRayWithZero_isotropic (hΩ : ∀r,Ω r r=0) (r : M) :
    ∀p∈positiveRayWithZero r,∀q∈positiveRayWithZero r,Ω p q=0 := by
  intro p hp q hq
  rcases hp with rfl|hp
  · simp
  rcases hq with rfl|hq
  · simp
  exact hp.pair_zero Ω hq (hΩ r)
variable (C : (I → ℤ) →+ M)
lemma closed_ray_crossing (hΩ : ∀r,Ω r r=0) (r : M)
    {F : PowerSeries (Torus LaurentRay.vUnit Ω)}
    (hF : InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C (OnPositiveRay r)) F) :
    (∀m,0≤Ω r m → IntegralPositive Ω
      (F*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1)) ∧
    (∀m,Ω r m≤0 → IntegralPositive Ω
      (invOfUnit F 1*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*F)) := by
  have hFF : InPrecisionClosure LaurentRay.vUnit Ω
      (literalRootProducts Ω C (fun p=>p∈positiveRayWithZero r)) F:=
    hF.mono LaurentRay.vUnit Ω (literalRootProducts_allowed_mono Ω C _ _ (fun n hn p hr hp=>Or.inr hp))
  have H:=closed_isotropic_adjoint Ω C (positiveRayWithZero r) hΩ
    (positiveRayWithZero_isotropic Ω hΩ r) hFF
  constructor
  · intro m hm
    apply H.1 m
    intro p hp
    rcases hp with rfl|hp
    · simp
    exact hp.pair_nonneg Ω (OnPositiveRay.refl m) hm
  · intro m hm
    apply H.2 m
    intro p hp
    rcases hp with rfl|hp
    · simp
    have hh:=hp.eval (incomingCovector Ω m)
    by_contra hx
    have hp0 : (0:ℝ)<Ω p m:=by exact_mod_cast (lt_of_not_ge hx)
    have hr0:=hh.1.mp hp0
    change (0:ℝ)<Ω r m at hr0
    have hr1 : (Ω r m:ℝ)≤0:=by exact_mod_cast hm
    linarith
variable (e : M →+ E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in
theorem global_ray_closure (F : CompletedPositive LaurentRay.vUnit Ω C)
    (incoming : PositiveIncomingPrescription Ω C F) (r : M) (d : ℕ)
    (hd : 0<d) (hr : HasRootDegree C d r) (h : Module.Dual ℝ E)
    (hg : ∀N,RayGeneric C N r (h.toAddMonoidHom.comp e)) :
    InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C (OnPositiveRay r))
      (chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) F).val := by
  apply inPrecisionClosure_of_cuts
  intro N
  exact positive_walls_through Ω C e he B hB hcomp L hdeg F incoming N r d hd hr h (hg N)
include he hB hcomp hdeg in
theorem literal_global_positive_crossings (l : List (WallUnitDatum M))
    (hl : ∀u∈l,u.Allowed C (fun _=>True)) (r : M) (d : ℕ)
    (hd : 0<d) (hr : HasRootDegree C d r) (h : Module.Dual ℝ E)
    (hg : ∀N,RayGeneric C N r (h.toAddMonoidHom.comp e)) :
    let F:=(chartZero LaurentRay.vUnit Ω C (h.toAddMonoidHom.comp e) (literalTotalTransport Ω C l)).val
    (∀m,0≤Ω r m → IntegralPositive Ω
      (F*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*invOfUnit F 1)) ∧
    (∀m,Ω r m≤0 → IntegralPositive Ω
      (invOfUnit F 1*PowerSeries.C (Torus.X LaurentRay.vUnit Ω m)*F)) := by
  have hΩ : ∀m,Ω m m=0:=by
    intro m
    have H:=(hcomp m m).symm.trans (hB (e m))
    exact_mod_cast H
  exact closed_ray_crossing Ω C hΩ r (global_ray_closure Ω C e he B hB hcomp L hdeg _
    (literalTotalTransport_prescription Ω C hΩ l hl) r d hd hr h hg)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
