import OAI.Algebra.FormalGroup.Honda.UniversalTransport

namespace OAI

noncomputable section

namespace HeightThree.HeightTransport
open MvPowerSeries HeightThree.HondaTarget HeightThree.CoordinateTransport
open HeightThree.HondaJets HeightThree.DeformationRigidity
variable {R S : Type*} [CommRing R] [CommRing S]

lemma strict_jet (f : PowerSeries R) (h0 : f.constantCoeff=0) (h1 : f.coeff 1=1) :
    EqJet 2 f PowerSeries.X := by
  intro d hd
  have he : d=Finsupp.single () (d ()) := Finsupp.unique_single d
  rw [he] at hd ⊢
  simp only [Finsupp.degree_single] at hd
  have hj : d ()=0 ∨ d ()=1 := by omega
  rcases hj with hj | hj
  · rw [hj]; change PowerSeries.coeff 0 f=PowerSeries.coeff 0 PowerSeries.X
    simpa using h0
  · rw [hj]; change PowerSeries.coeff 1 f=PowerSeries.coeff 1 PowerSeries.X
    simpa using h1

lemma strict_inverse (c : Coordinate R) (hc : c.series.coeff 1=1) :
    c.inverse.coeff 1=1 := by
  simpa [hc] using c.linear_inverse

lemma homogeneous_uni (f : PowerSeries R) (n : ℕ) :
    (f : MvPowerSeries Unit R).homogeneousComponent n=
      PowerSeries.C (f.coeff n)*PowerSeries.X^n := by
  apply PowerSeries.ext
  intro j
  change coeff (Finsupp.single () j) (f.homogeneousComponent n)=_
  rw [coeff_homogeneousComponent]
  simp only [Finsupp.degree_single]
  change (if j=n then f.coeff j else 0)=_
  rw [PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow]
  by_cases hj : j=n
  · subst j; simp
  · simp [hj]

lemma strict_subst_leading (P u : PowerSeries R) (n : ℕ)
    (hP : EqJet n P 0) (hu0 : u.constantCoeff=0) (hu1 : u.coeff 1=1) :
    EqJet (n+1) (P.subst u) P := by
  have hlead := leading_part P n hP
  rw [homogeneous_uni] at hlead
  have hs := hlead.subst_left (fun _ : Unit=>u)
    (PowerSeries.HasSubst.of_constantCoeff_zero hu0).const (fun _=>hu0)
  change EqJet (n+1) (P.subst u) ((PowerSeries.C (P.coeff n)*PowerSeries.X^n).subst u) at hs
  rw [PowerSeries.subst_mul (.of_constantCoeff_zero hu0),
    PowerSeries.subst_C,
    PowerSeries.subst_pow (.of_constantCoeff_zero hu0),
    PowerSeries.subst_X (.of_constantCoeff_zero hu0)] at hs
  have hp := (strict_jet u hu0 hu1).pow_leading hu0 (by simp [PowerSeries.X]) n
  have hh := hp.mul_left (PowerSeries.C (P.coeff n))
  exact (hs.trans hh).trans hlead.symm

lemma strict_outer_leading (P u : PowerSeries R) (n : ℕ)
    (hP : EqJet n P 0) (hP0 : P.constantCoeff=0)
    (hu0 : u.constantCoeff=0) (hu1 : u.coeff 1=1) :
    EqJet (n+1) (u.subst P) P := by
  have hh := subst_first_order u n (fun _ : Unit=>P) (fun _ : Unit=>(0 : PowerSeries R))
    (fun _=>hP0) (by simp) (fun _=>hP)
  have hzero : u.subst (0 : PowerSeries R)=0 := by
    exact PowerSeries.subst_zero_of_constantCoeff_zero hu0
  change EqJet (n+1) (u.subst P-u.subst (0 : PowerSeries R))
    (∑i : Unit, C (coeff (Finsupp.single i 1) u)*(P-0)) at hh
  simpa only [hzero,sub_zero,Fintype.sum_unique,show coeff (Finsupp.single () 1) u=1 from hu1,
    map_one,one_mul] using hh

lemma multiplication_transport (c : Coordinate R) (F : FormalGroup R) (n : ℕ) :
    multiplicationSeries (c.transport F) n=
      c.series.subst ((multiplicationSeries F n).subst c.inverse) := by
  have hh := coordinate_multiplication F (c.transport F) (c.iso F) n
  change c.series.subst (multiplicationSeries F n)=
    (multiplicationSeries (c.transport F) n).subst c.series at hh
  have hh' := congrArg (fun z : PowerSeries R=>z.subst c.inverse) hh
  rw [PowerSeries.subst_comp_subst_apply (.of_constantCoeff_zero (multiplication_constant F n)) c.inv_hasSubst,
    PowerSeries.subst_comp_subst_apply c.hasSubst c.inv_hasSubst,c.left_inv,
    PowerSeries.X_subst] at hh'
  exact hh'.symm

lemma conjugate_leading (c : Coordinate R) (hc : c.series.coeff 1=1)
    (P : PowerSeries R) (n : ℕ) (hP0 : P.constantCoeff=0) (hP : EqJet n P 0) :
    EqJet (n+1) (c.series.subst (P.subst c.inverse)) P := by
  have he := strict_subst_leading P c.inverse n hP c.zero_inverse (strict_inverse c hc)
  have hz : (P.subst c.inverse).constantCoeff=0 :=
    PowerSeries.constantCoeff_subst_eq_zero c.zero_inverse P hP0
  have hh := strict_outer_leading (P.subst c.inverse) c.series n
    ((he.mono (by omega)).trans hP) hz c.zero_series hc
  exact hh.trans he

end HeightThree.HeightTransport

namespace HeightThree.HeightTransport
open MvPowerSeries HeightThree.HondaTarget HeightThree.CoordinateTransport
open HeightThree.HondaJets HeightThree.DeformationRigidity
variable {R S : Type*} [CommRing R] [CommRing S]

lemma jet_zero_of_coeff (P : PowerSeries R) (n : ℕ) (hP : ∀j<n,P.coeff j=0) :
    EqJet n P 0 := by
  intro d hd
  rw [Finsupp.unique_single d] at hd ⊢
  simp only [Finsupp.degree_single] at hd
  change PowerSeries.coeff (d ()) P=0
  exact hP (d ()) hd

lemma low_leading_transport (c : Coordinate R) (hc : c.series.coeff 1=1)
    (F : FormalGroup R) (q n : ℕ) (hlow : ∀j<n,(multiplicationSeries F q).coeff j=0) :
    (∀j<n,(multiplicationSeries (c.transport F) q).coeff j=0) ∧
    (multiplicationSeries (c.transport F) q).coeff n=(multiplicationSeries F q).coeff n := by
  have hh := conjugate_leading c hc (multiplicationSeries F q) n (multiplication_constant F q)
    (jet_zero_of_coeff _ n hlow)
  rw [←multiplication_transport] at hh
  constructor
  · intro j hj
    have he := hh (Finsupp.single () j) (by simpa using (show j<n+1 by omega))
    exact he.trans (hlow j hj)
  · exact hh (Finsupp.single () n) (by simp)

lemma strict_map (c : Coordinate R) (hc : c.series.coeff 1=1) (π : R →+* S) :
    (c.map π).series.coeff 1=1 := by
  change π (c.series.coeff 1)=1
  rw [hc,map_one]

lemma heightCoordinates_transport {K : Type*} [CommRing K] (p : ℕ)
    (G : FormalGroup (Base K)) (hg : HeightCoordinates p G)
    (c : Coordinate (Base K)) (hc : c.series.coeff 1=1) :
    HeightCoordinates p (c.transport G) := by
  let I : Ideal (Base K) := Ideal.span ({X 0} : Set (Base K))
  let π := Ideal.Quotient.mk I
  have h₁ := low_leading_transport c hc G p p hg.1
  have hlow : ∀j<p^2,(multiplicationSeries (G.map π) p).coeff j=0 := by
    intro j hj
    rw [multiplication_map]
    change π ((multiplicationSeries G p).coeff j)=0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hg.2.2.1 j hj)
  have h₂ := low_leading_transport (c.map π) (strict_map c hc π) (G.map π) p (p^2) hlow
  have hmap : (c.map π).transport (G.map π)=(c.transport G).map π :=
    (c.transport_map G π).symm
  rw [hmap,multiplication_map] at h₂
  refine ⟨h₁.1,h₁.2.trans hg.2.1,?_,?_⟩
  · intro j hj
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact h₂.1 j hj
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    change π ((multiplicationSeries (c.transport G) p).coeff (p^2)-X 1)=0
    rw [map_sub]
    have he : π ((multiplicationSeries (c.transport G) p).coeff (p^2))=
        π ((multiplicationSeries G p).coeff (p^2)) := by
      simpa only [multiplication_map,PowerSeries.coeff_map] using h₂.2
    rw [he,←map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hg.2.2.2

end HeightThree.HeightTransport

end

end OAI
