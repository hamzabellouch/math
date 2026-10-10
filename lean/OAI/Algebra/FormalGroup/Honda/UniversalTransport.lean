import OAI.Algebra.FormalGroup.Honda.Classification

namespace OAI

universe uK

noncomputable section

namespace HeightThree.UniversalTransport
open MvPowerSeries HeightThree.HondaTarget HeightThree.CoordinateTransport
open HeightThree.ArtinianUniversality HeightThree.NilpotentTower
variable {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]

lemma transport_symm (c : Coordinate R) (F : FormalGroup R) :
    c.symm.transport (c.transport F)=F := by
  exact Coordinate.transport_ofIso (CoordinateIso.symm (c.iso F))

lemma symm_transport (c : Coordinate R) (F : FormalGroup R) :
    c.transport (c.symm.transport F)=F := by
  exact transport_symm c.symm F

lemma coordinate_map_map (c : Coordinate R) (π : R →+* S) (ρ : S →+* K) :
    (c.map π).map ρ=c.map (ρ.comp π) := by
  apply Coordinate.map_eq_of_series_eq
  exact HeightThree.CoordinateTransport.unimap_comp π ρ c.series

lemma coordinate_map_id (c : Coordinate R) : c.map (RingHom.id R)=c := by
  apply Coordinate.map_eq_of_series_eq
  exact congrFun PowerSeries.map_id c.series

lemma coordinate_map_symm (c : Coordinate R) (π : R →+* S) :
    c.symm.map π=(c.map π).symm := rfl

lemma unimap_subst (π : R →+* S) (f g : PowerSeries R) (hg : g.constantCoeff=0) :
    PowerSeries.map π (f.subst g)=(PowerSeries.map π f).subst (PowerSeries.map π g) :=
  PowerSeries.map_subst (.of_constantCoeff_zero hg) f

lemma iso_trans_series {F G H : FormalGroup R} (e : CoordinateIso F G) (d : CoordinateIso G H) :
    (CoordinateIso.trans e d).series=d.series.subst e.series := rfl
lemma iso_symm_series {F G : FormalGroup R} (e : CoordinateIso F G) :
    (CoordinateIso.symm e).series=e.inverse := rfl
lemma iso_series (c : Coordinate R) (F : FormalGroup R) : (c.iso F).series=c.series := rfl
lemma iso_inverse (c : Coordinate R) (F : FormalGroup R) : (c.iso F).inverse=c.inverse := rfl

lemma framed_transport (ρ : R →+* K) (c : Coordinate R) {F G : FormalGroup R}
    (he : FramedEquivalent ρ F G) :
    FramedEquivalent ρ (c.transport F) (c.transport G) := by
  obtain ⟨e,he⟩ := he
  refine ⟨CoordinateIso.trans (CoordinateIso.symm (c.iso F))
    (CoordinateIso.trans e (c.iso G)),?_⟩
  rw [iso_trans_series,iso_trans_series,iso_symm_series,iso_series,iso_inverse]
  rw [unimap_subst ρ _ c.inverse c.zero_inverse,
    unimap_subst ρ c.series e.series e.zero_series,he,PowerSeries.X_subst]
  exact (c.map ρ).left_inv

lemma framed_transport_iff (ρ : R →+* K) (c : Coordinate R) (F G : FormalGroup R) :
    FramedEquivalent ρ (c.transport F) (c.transport G) ↔ FramedEquivalent ρ F G := by
  constructor
  · intro h
    have hh := framed_transport ρ c.symm h
    rwa [transport_symm,transport_symm] at hh
  · exact framed_transport ρ c

lemma scalar_coordinate_map [Algebra K R] [Algebra K S] (c : Coordinate K) (f : R →ₐ[K] S) :
    (c.map (algebraMap K R)).map f.toRingHom=c.map (algebraMap K S) := by
  rw [coordinate_map_map]
  congr 1
  ext z
  exact f.commutes z

lemma scalar_coordinate_reduce [Algebra K R] (c : Coordinate K) (ρ : R →ₐ[K] K) :
    (c.map (algebraMap K R)).map ρ.toRingHom=c := by
  rw [scalar_coordinate_map]
  exact coordinate_map_id c

end HeightThree.UniversalTransport

namespace HeightThree.UniversalTransport
open MvPowerSeries HeightThree.HondaTarget HeightThree.CoordinateTransport
open HeightThree.ArtinianUniversality HeightThree.NilpotentTower
variable {K : Type uK} [Field K]

theorem isUniversal_transport (Γ : FormalGroup K) (G : FormalGroup (Base K))
    (hG : IsUniversal Γ G) (c : Coordinate K) :
    IsUniversal (c.transport Γ) ((c.map (algebraMap K (Base K))).transport G) := by
  intro R _ _ _ _ ρ F hF hred
  let cR := c.map (algebraMap K R)
  let F' := cR.symm.transport F
  have hcR : cR.map ρ.toRingHom=c := scalar_coordinate_reduce c ρ
  have hF' : F'.IsComm := by
    have := hF
    exact inferInstance
  have hr : F'.map ρ.toRingHom=Γ := by
    rw [show F'=cR.symm.transport F from rfl,Coordinate.transport_map,
      coordinate_map_symm,hcR,hred,transport_symm]
  obtain ⟨f,hf,huniq⟩ := hG R ρ F' hF' hr
  refine ⟨f,⟨hf.1,?_⟩,?_⟩
  · have he := framed_transport ρ.toRingHom cR hf.2
    change FramedEquivalent _ _ (cR.transport (cR.symm.transport F)) at he
    rw [symm_transport] at he
    rw [Coordinate.transport_map,scalar_coordinate_map]
    exact he
  · intro g hg
    apply huniq g
    refine ⟨hg.1,?_⟩
    have he := hg.2
    rw [Coordinate.transport_map,scalar_coordinate_map] at he
    have he' := framed_transport ρ.toRingHom cR.symm he
    rw [transport_symm] at he'
    exact he'

end HeightThree.UniversalTransport

end

end OAI
