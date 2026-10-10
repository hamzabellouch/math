import Mathlib
import OAI.Geometry.Cannon.Boundary.ImageAwayPuncture
import OAI.Geometry.Cannon.Modulus.RadialCellEnergy
import OAI.Geometry.Cannon.Uniformization.AnnulusFamily

namespace OAI

section
section
section
noncomputable section
namespace CannonCarrierCharging
open Set Metric Topology CannonCells CannonUniformization

variable {X : Type*} [MetricSpace X]

lemma radial_level_preimage {Y : Type*} [PseudoMetricSpace Y] (f : C(X,Y)) (E : Set X) (hE : IsPreconnected E)
    (p : Y) {u v : X} (hu : u∈E) (hv : v∈E) {a b : ℝ}
    (hu' : dist (f u) p≤a) (hv' : b≤dist (f v) p) :
    ∀ t∈Icc a b,∃ x∈E,f x∈sphere p t := by
  intro t ht
  have hc : ContinuousOn (fun x=>dist (f x) p) E :=
    (f.continuous.dist continuous_const).continuousOn
  obtain ⟨x,hx,hxt⟩:=hE.intermediate_value hu hv hc ⟨hu'.trans ht.1,ht.2.trans hv'⟩
  exact ⟨x,hx,hxt⟩

theorem radial_continua_carrier_crossing {Y κ : Type*} [PseudoMetricSpace Y]
    (f : C(X,Y)) (A : κ → Set X) (K : κ → Set Y)
    (hpre : ∀ S : Set Y,f ⁻¹' S⊆⋃(d : {d : κ // (S∩K d).Nonempty}),A d.val)
    (E F : Set X) (hE : IsPreconnected E) (hF : IsPreconnected F)
    (o : X) (r R : ℝ) (hEin : E⊆closedBall o r) (hFout : F⊆(ball o R)ᶜ)
    (p : Y) (a b : ℝ)
    (hErange : ∃ u∈E,∃ v∈E,dist (f u) p≤a ∧ b≤dist (f v) p)
    (hFrange : ∃ u∈F,∃ v∈F,dist (f u) p≤a ∧ b≤dist (f v) p) :
    ∀ t∈Icc a b,
      ∃ x∈⋃(d : {d : κ // (sphere p t∩K d).Nonempty}),A d.val,
      ∃ y∈⋃(d : {d : κ // (sphere p t∩K d).Nonempty}),A d.val,
        ∀ γ : Path x y,range γ∈annulusFamily o r R := by
  obtain ⟨u,hu,v,hv,hu',hv'⟩:=hErange
  obtain ⟨u',huF,v',hvF,huF',hvF'⟩:=hFrange
  intro t ht
  obtain ⟨x,hx,hfx⟩:=radial_level_preimage f E hE p hu hv hu' hv' t ht
  obtain ⟨y,hy,hfy⟩:=radial_level_preimage f F hF p huF hvF huF' hvF' t ht
  refine ⟨x,hpre _ hfx,y,hpre _ hfy,?_⟩
  intro γ
  exact ⟨x,y,γ,rfl,hEin hx,le_of_not_gt (hFout hy)⟩

lemma circle_carriers_preconnected {κ : Type*}
    (A : κ → Set X) (K : κ → Set ℂ)
    (hc : ∀ S : Set ℂ,IsPreconnected S →
      IsPreconnected (⋃(d : {d : κ // (S∩K d).Nonempty}),A d.val))
    (p : ℂ) (t : ℝ) :
    IsPreconnected (⋃(d : {d : κ // (sphere p t∩K d).Nonempty}),A d.val) := by
  apply hc
  apply isPreconnected_sphere
  simp
end CannonCarrierCharging

namespace CannonCarrierCharging
open Set Metric Topology CannonUniformization
open scoped OnePoint

variable {X : Type*} [MetricSpace X]

lemma spherical_radial_level_preimage (f : C(X,OnePoint ℂ))
    (E : Set X) (hE : IsPreconnected E) (p : ℂ)
    {u v : X} (hu : u∈E) (hv : v∈E) {a b : ℝ}
    (hu' : f u∈((↑) '' closedBall p a : Set (OnePoint ℂ)))
    (hv' : f v∉((↑) '' ball p b : Set (OnePoint ℂ))) :
    ∀ t∈Icc a b,∃ x∈E,f x∈((↑) '' sphere p t : Set (OnePoint ℂ)) := by
  intro t ht
  let U : Set (OnePoint ℂ):=((↑) '' closedBall p t)
  let V : Set (OnePoint ℂ):=((↑) '' ball p t)ᶜ
  have hU : IsClosed U := ((isCompact_closedBall p t).image OnePoint.continuous_coe).isClosed
  have hV : IsClosed V := (OnePoint.isOpenMap_coe _ isOpen_ball).isClosed_compl
  have huc : f u∈U := by
    obtain ⟨z,hz,hzf⟩:=hu'
    exact ⟨z,(mem_closedBall.mp hz).trans ht.1,hzf⟩
  have hvc : f v∈V := by
    intro h
    apply hv'
    obtain ⟨z,hz,hzf⟩:=h
    exact ⟨z,(mem_ball.mp hz).trans_le ht.2,hzf⟩
  have hcover : f '' E⊆U∪V := by
    intro y _
    by_cases hy : y∈((↑) '' ball p t : Set (OnePoint ℂ))
    · obtain ⟨z,hz,rfl⟩:=hy
      exact Or.inl ⟨z,(mem_ball.mp hz).le,rfl⟩
    · exact Or.inr hy
  obtain ⟨q,⟨x,hx,hxq⟩,hqU,hqV⟩:=isPreconnected_closed_iff.mp
    (hE.image f f.continuous.continuousOn) U V hU hV hcover
    ⟨f u,mem_image_of_mem f hu,huc⟩ ⟨f v,mem_image_of_mem f hv,hvc⟩
  obtain ⟨z,hz,hzq⟩:=hqU
  have hnot : ¬dist z p<t := by
    intro hh
    exact hqV ⟨z,hh,hzq⟩
  refine ⟨x,hx,z,le_antisymm hz (le_of_not_gt hnot),?_⟩
  exact hzq.trans hxq.symm

theorem spherical_continua_carrier_crossing {κ : Type*}
    (f : C(X,OnePoint ℂ)) (A : κ → Set X) (K : κ → Set (OnePoint ℂ))
    (hpre : ∀ S : Set (OnePoint ℂ),f ⁻¹' S⊆
      ⋃(d : {d : κ // (S∩K d).Nonempty}),A d.val)
    (E F : Set X) (hE : IsPreconnected E) (hF : IsPreconnected F)
    (o : X) (r R : ℝ) (hEin : E⊆closedBall o r) (hFout : F⊆(ball o R)ᶜ)
    (p : ℂ) (a b : ℝ)
    (hErange : ∃ u∈E,∃ v∈E,
      f u∈((↑) '' closedBall p a : Set (OnePoint ℂ)) ∧
      f v∉((↑) '' ball p b : Set (OnePoint ℂ)))
    (hFrange : ∃ u∈F,∃ v∈F,
      f u∈((↑) '' closedBall p a : Set (OnePoint ℂ)) ∧
      f v∉((↑) '' ball p b : Set (OnePoint ℂ))) :
    ∀ t∈Icc a b,
      ∃ x∈⋃(d : {d : κ // (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty}),A d.val,
      ∃ y∈⋃(d : {d : κ // (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty}),A d.val,
        ∀ γ : Path x y,range γ∈annulusFamily o r R := by
  obtain ⟨u,hu,v,hv,hu',hv'⟩:=hErange
  obtain ⟨u',huF,v',hvF,huF',hvF'⟩:=hFrange
  intro t ht
  obtain ⟨x,hx,hfx⟩:=spherical_radial_level_preimage f E hE p hu hv hu' hv' t ht
  obtain ⟨y,hy,hfy⟩:=spherical_radial_level_preimage f F hF p huF hvF huF' hvF' t ht
  refine ⟨x,hpre _ hfx,y,hpre _ hfy,?_⟩
  intro γ
  exact ⟨x,y,γ,rfl,hEin hx,le_of_not_gt (hFout hy)⟩

lemma spherical_circle_carriers_preconnected {κ : Type*}
    (A : κ → Set X) (K : κ → Set (OnePoint ℂ))
    (hc : ∀ S : Set (OnePoint ℂ),IsPreconnected S →
      IsPreconnected (⋃(d : {d : κ // (S∩K d).Nonempty}),A d.val))
    (p : ℂ) (t : ℝ) :
    IsPreconnected
      (⋃(d : {d : κ // (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty}),A d.val) := by
  apply hc
  exact (isPreconnected_sphere (by simp) p t).image _ OnePoint.continuous_coe.continuousOn
end CannonCarrierCharging

end
end
section
noncomputable section
namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonCarrierCharging CannonUniformization
open scoped OnePoint

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_annular_circle_carriers (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ L c : ℝ,1≤L ∧ 0<c ∧ c≤1 ∧ ∀ {κ : Type*},
      ∀ A : κ → Set (Boundary D),∀ K : κ → Set (OnePoint ℂ),
      ∀ f : C(Boundary D,OnePoint ℂ),
      (∀ S : Set (OnePoint ℂ),f ⁻¹' S⊆
        ⋃(d : {d : κ // (S∩K d).Nonempty}),A d.val) →
      ∀ (o a₀ b₀ z₀ : Boundary D) (r R : ℝ),0<r → 0<R →
        dist o a₀≤r → R≤dist o b₀ → R≤dist o z₀ →
      ∀ (p : ℂ) (a b : ℝ),
        f o∈((↑) '' closedBall p a : Set (OnePoint ℂ)) →
        f a₀∉((↑) '' ball p b : Set (OnePoint ℂ)) →
        f b₀∈((↑) '' closedBall p a : Set (OnePoint ℂ)) →
        f z₀∉((↑) '' ball p b : Set (OnePoint ℂ)) →
      ∀ t∈Icc a b,
        ∃ x∈⋃(d : {d : κ // (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty}),A d.val,
        ∃ y∈⋃(d : {d : κ // (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty}),A d.val,
          ∀ γ : Path x y,range γ∈annulusFamily o (L*r) (c*R) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨L,hL,hinner⟩:=boundary_controlled_paths D hδ φ
  obtain ⟨c,hc,hc1,houter⟩:=boundary_outside_paths D hδ φ
  refine ⟨L,c,hL,hc,hc1,?_⟩
  intro κ A K f hpre o a₀ b₀ z₀ r R hr hR ha₀ hb₀ hz₀ p a b ho ha hb hz
  have hi:=hinner o o a₀ r hr (by change dist o o≤r; simpa using hr.le) ha₀
  have ho':=houter o b₀ z₀ R hR hb₀ hz₀
  let γ : Path o a₀:=hi.somePath
  let η : Path b₀ z₀:=ho'.somePath
  have hγ : IsPreconnected (range γ) := isPreconnected_range γ.continuous
  have hη : IsPreconnected (range η) := isPreconnected_range η.continuous
  have hhγ : range γ⊆closedBall o (L*r) := by
    rintro x ⟨t,rfl⟩
    have hh:=hi.somePath_mem t
    change dist o (γ t)<L*r at hh
    exact (dist_comm (γ t) o).le.trans hh.le
  have hhη : range η⊆(ball o (c*R))ᶜ := by
    rintro x ⟨t,rfl⟩ hx
    have hh:=ho'.somePath_mem t
    change c*R<dist o (η t) at hh
    have hx':=mem_ball.mp hx
    rw [dist_comm] at hx'
    exact (not_lt_of_ge hh.le) hx'
  exact spherical_continua_carrier_crossing f A K hpre (range γ) (range η) hγ hη
    o (L*r) (c*R) hhγ hhη p a b
    ⟨o,⟨0,γ.source⟩,a₀,⟨1,γ.target⟩,ho,ha⟩
    ⟨b₀,⟨0,η.source⟩,z₀,⟨1,η.target⟩,hb,hz⟩
end CannonRelease

end
end
section
noncomputable section
open Set Metric Topology
open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable
namespace CannonRadialEnergy

theorem local_radial_cell_energy_budget {ι Y : Type*} [Fintype ι] [PseudoMetricSpace Y]
    {a b L P : ℝ} (hab : a≤b) (hL : 0≤L)
    (p : Y) (c : ι → Y) (r w : ι → ℝ) (U : ι → Set Y)
    (hr : ∀ i,0≤r i) (hw : ∀ i,0≤w i)
    (hcell : ∀ i,(∃ t∈Icc a b,(U i∩sphere p t).Nonempty) →
      U i⊆closedBall (c i) (L*r i))
    (hbudget : (∑ i,if ∃ t∈Icc a b,(U i∩sphere p t).Nonempty then r i^2 else 0)≤P)
    (hadm : ∀ t∈Icc a b,1≤∑ i,if (U i∩sphere p t).Nonempty then w i else 0) :
    (b-a)^2≤4*L^2*P*∑ i,w i^2 := by
  classical
  let act : ι → Prop:=fun i=>∃ t∈Icc a b,(U i∩sphere p t).Nonempty
  let r' : ι → ℝ:=fun i=>if act i then r i else 0
  let U' : ι → Set Y:=fun i=>if act i then U i else ∅
  apply radial_cell_energy_budget hab hL p c r' w U'
  · intro i
    dsimp only [r']
    split_ifs
    · exact hr i
    · exact le_rfl
  · exact hw
  · intro i
    by_cases hi : act i
    · simpa only [U',r',ite_eq_left hi] using hcell i hi
    · simp only [U',r',ite_eq_right hi,empty_subset]
  · simpa only [r',ite_pow,zero_pow (by decide : 2≠0)] using hbudget
  · intro t ht
    convert hadm t ht using 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : act i
    · simp only [U',ite_eq_left hi]
    · have hn : ¬(U i∩sphere p t).Nonempty:=fun h=>hi ⟨t,ht,h⟩
      simp [U',hi,hn]
end CannonRadialEnergy

namespace CannonCarrierCharging
open CannonCells CannonDuality

theorem metric_carrier_modulus_bound {X Y ι ν κ : Type*} [MetricSpace X]
    [PseudoMetricSpace Y] [LocallyPathConnectedSpace X] [Fintype ι] [Fintype ν]
    [DecidableEq ι] [DecidableEq ν]
    (A : κ → Set X) (K : κ → Set Y) (U : ν → Set Y)
    (s : κ → ν) (v : ν → X) (q : ι → X)
    (mesh η D : ℝ) (hη : 0<η)
    (hdiam : ∀ d,∀ x∈A d,dist x (v (s d))≤D)
    (hstar : ∀ d,K d⊆U (s d))
    (F : Set (Set X)) (hFn : ∀ E∈F,E.Nonempty)
    (hcover : ∀ x,∃ i,x∈ball (q i) (2*mesh))
    {a b L P : ℝ} (hab : a≤b) (hL : 0≤L) (hP : 0≤P)
    (p : Y) (c : ν → Y) (rad : ν → ℝ) (hr : ∀ j,0≤rad j)
    (hcell : ∀ j,(∃ t∈Icc a b,(U j∩sphere p t).Nonempty) →
      U j⊆closedBall (c j) (L*rad j))
    (hbudget : (∑ j,if ∃ t∈Icc a b,(U j∩sphere p t).Nonempty then rad j^2 else 0)≤P)
    (hconn : ∀ t∈Icc a b,IsPreconnected
      (⋃ (d : {d : κ // (sphere p t∩K d).Nonempty}),A d.val))
    (hcross : ∀ t∈Icc a b,
      ∃ x∈⋃ (d : {d : κ // (sphere p t∩K d).Nonempty}),A d.val,
      ∃ y∈⋃ (d : {d : κ // (sphere p t∩K d).Nonempty}),A d.val,
        ∀ γ : Path x y,range γ∈F)
    (kr kc : ℕ)
    (hrow : ∀ j,(Finset.univ.filter (fun i=>dist (q i) (v j)<2*mesh+η+D)).card≤kr)
    (hcol : ∀ i,(Finset.univ.filter (fun j=>dist (q i) (v j)<2*mesh+η+D)).card≤kc) :
    (b-a)^2≤4*L^2*P*(kr:ℝ)*kc*modulus (fun i=>ball (q i) (2*mesh)) F := by
  classical
  have hF : F.Nonempty := by
    obtain ⟨x,hx,y,hy,hxy⟩:=hcross a ⟨le_rfl,hab⟩
    obtain ⟨γ,-⟩:=CannonFiniteCarrier.path_in_open_enlargement (hconn a ⟨le_rfl,hab⟩)
      isOpen_thickening (self_subset_thickening hη _) hx hy
    exact ⟨range γ,hxy γ⟩
  obtain ⟨_,w,hw,he⟩:=modulus_minimum (fun i=>ball (q i) (2*mesh)) hcover hF hFn
  let J : ν → Finset ι:=fun j=>Finset.univ.filter (fun i=>dist (q i) (v j)<2*mesh+η+D)
  let W : ν → ℝ:=fun j=>∑ i∈J j,w i
  have hW : ∀ j,0≤W j := fun j=>Finset.sum_nonneg fun i _=>hw.1 i
  have hadm : ∀ t∈Icc a b,1≤∑ j,if (U j∩sphere p t).Nonempty then W j else 0 := by
    intro t ht
    obtain ⟨x,hx,y,hy,hxy⟩:=hcross t ht
    have hh:=carrier_admissible_charging A K U s v q (sphere p t) mesh η D hη hdiam hstar
      (hconn t ht) hx hy F hxy w hw
    simpa only [W,J,Finset.sum_filter,inter_comm] using hh
  have hrad:=CannonRadialEnergy.local_radial_cell_energy_budget hab hL p c rad W U
    hr hW hcell hbudget hadm
  have heW:=CannonTransfer.overlap_energy J (fun i=>w i) kr kc hrow (by
    intro i
    simpa only [J,Finset.mem_filter,Finset.mem_univ,true_and] using hcol i)
  have hnorm : ∑ i,(w i)^2=‖w‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs,sq_abs]
  calc
    _ ≤ 4*L^2*P*∑ j,W j^2 := hrad
    _ ≤ 4*L^2*P*((kr:ℝ)*kc*∑ i,(w i)^2) :=
      mul_le_mul_of_nonneg_left heW (by positivity)
    _ = _ := by rw [hnorm,he]; ring
end CannonCarrierCharging

end
end
section
noncomputable section
namespace CannonRoundRadial
open Set Metric Topology
open scoped InnerProductSpace

abbrev Ambient:=EuclideanSpace ℝ (Fin 3)
abbrev Round:=sphere (0:Ambient) 1

theorem metric_sphere_preconnected (p : Round) (t : ℝ) :
    IsPreconnected (sphere p t) := by
  have hp : ‖(p:Ambient)‖=1:=by simpa only [mem_sphere,dist_zero_right] using p.property
  have hbound (x : Round) : dist x p≤2 := by
    have hx : ‖(x:Ambient)‖=1:=by simpa only [mem_sphere,dist_zero_right] using x.property
    have h:=dist_triangle (x:Ambient) 0 (p:Ambient)
    change dist (x:Ambient) (p:Ambient)≤2
    simpa only [dist_zero_right,dist_zero_left,hx,hp,one_add_one_eq_two] using h
  by_cases ht : 0≤t ∧ t≤2
  swap
  · have he : sphere p t=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hx' : dist x p=t:=hx
      exact ht ⟨hx' ▸ dist_nonneg,hx' ▸ hbound x⟩
    rw [he]
    exact isPreconnected_empty
  have hp0 : (p:Ambient)≠0:=by intro h; simp [h] at hp
  let V : Submodule ℝ Ambient:=(ℝ ∙ (p:Ambient))ᗮ
  let a : ℝ:=1-t^2/2
  have hamin : -1≤a := by
    have hm:=mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
    dsimp only [a]
    nlinarith
  have hamax : a≤1 := by dsimp only [a]; nlinarith [sq_nonneg t]
  have hRa : 0≤1-a^2 := by
    have hh:=mul_nonneg (show 0≤1-a by linarith) (show 0≤1+a by linarith)
    nlinarith
  let R : ℝ:=Real.sqrt (1-a^2)
  have hR : 0≤R:=Real.sqrt_nonneg _
  have hR2 : R^2=1-a^2:=Real.sq_sqrt hRa
  have hpp : inner ℝ (p:Ambient) (p:Ambient)=1 := by
    rw [real_inner_self_eq_norm_sq,hp]
    norm_num
  have orth (v : V) : inner ℝ (p:Ambient) (v:Ambient)=0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp v.property
  let g : V → Ambient:=fun v=>a•(p:Ambient)+(v:Ambient)
  have hg : Continuous g:=continuous_const.add (show Continuous fun v:V=>(v:Ambient) from continuous_subtype_val)
  have hnorm (v : V) : ‖g v‖^2=a^2+‖v‖^2 := by
    dsimp only [g]
    rw [norm_add_sq_real,real_inner_smul_left,orth,norm_smul,hp]
    simp only [mul_one,mul_zero,add_zero,Real.norm_eq_abs,sq_abs,Submodule.norm_coe]
  have hgp (v : V) : inner ℝ (g v) (p:Ambient)=a := by
    dsimp only [g]
    rw [inner_add_left,real_inner_smul_left,hpp,real_inner_comm,orth]
    ring
  have heq : (Subtype.val : Round → Ambient) '' sphere p t = g '' sphere (0:V) R := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      have hy0 : ‖(y:Ambient)‖=1:=by simpa only [mem_sphere,dist_zero_right] using y.property
      have hyp : ‖(y:Ambient)-(p:Ambient)‖=t:=by simpa only [mem_sphere,Subtype.dist_eq,dist_eq_norm] using hy
      have hi : inner ℝ (y:Ambient) (p:Ambient)=a := by
        have hh:=norm_sub_sq_real (y:Ambient) (p:Ambient)
        rw [hy0,hp,hyp] at hh
        dsimp only [a]
        nlinarith
      have hv : (y:Ambient)-a•(p:Ambient)∈V := by
        apply Submodule.mem_orthogonal_singleton_iff_inner_left.mpr
        rw [inner_sub_left,real_inner_smul_left,hi,hpp]
        ring
      let v : V:=⟨(y:Ambient)-a•(p:Ambient),hv⟩
      have he : g v=(y:Ambient) := by dsimp only [g,v]; module
      have hvn : ‖v‖=R := by
        have hh:=hnorm v
        rw [he,hy0] at hh
        nlinarith [norm_nonneg v]
      refine ⟨v,?_,he⟩
      simpa only [mem_sphere,dist_zero_right] using hvn
    · rintro ⟨v,hv,rfl⟩
      have hvn : ‖v‖=R:=by simpa only [mem_sphere,dist_zero_right] using hv
      have hgn : ‖g v‖=1 := by
        have hh:=hnorm v
        rw [hvn] at hh
        nlinarith [norm_nonneg (g v)]
      have hgt : ‖g v-(p:Ambient)‖=t := by
        have hh:=norm_sub_sq_real (g v) (p:Ambient)
        rw [hgn,hp,hgp] at hh
        dsimp only [a] at hh
        nlinarith [norm_nonneg (g v-(p:Ambient))]
      refine ⟨⟨g v,by simpa only [mem_sphere,dist_zero_right] using hgn⟩,?_,rfl⟩
      simpa only [mem_sphere,Subtype.dist_eq,dist_eq_norm] using hgt
  apply IsInducing.subtypeVal.isPreconnected_image.mp
  rw [heq]
  apply IsPreconnected.image _ _ hg.continuousOn
  apply isPreconnected_sphere
  let _ : Fact (Module.finrank ℝ Ambient=2+1):=⟨by simp [Ambient]⟩
  have hv : Module.finrank ℝ V=2:=Submodule.finrank_orthogonal_span_singleton hp0
  rw [←Module.finrank_eq_rank,hv]
  norm_num

theorem metric_circle_carriers_preconnected {X κ : Type*} [TopologicalSpace X]
    (A : κ → Set X) (K : κ → Set Round)
    (hc : ∀ S : Set Round,IsPreconnected S →
      IsPreconnected (⋃ (d : {d : κ // (S∩K d).Nonempty}),A d.val))
    (p : Round) (t : ℝ) :
    IsPreconnected (⋃ (d : {d : κ // (sphere p t∩K d).Nonempty}),A d.val) :=
  hc _ (metric_sphere_preconnected p t)
end CannonRoundRadial

end
end
end
end

end OAI
