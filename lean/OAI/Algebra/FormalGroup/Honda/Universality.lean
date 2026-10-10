import OAI.Algebra.FormalGroup.Honda.Evaluation

namespace OAI

universe uK uR

noncomputable section

namespace HeightThree.ArtinianUniversality
open MvPowerSeries HondaTarget DeformationRigidity CoordinateTransport NilpotentTower NilpotentEvaluation
variable {K R S : Type*} [Field K] [CommRing R] [CommRing S]

instance mapFormalGroup_isComm (F : FormalGroup R) [F.IsComm] (f : R →+* S) :
    (F.map f).IsComm where
  comm := by
    change F.toPowerSeries.map f = (F.toPowerSeries.map f).subst ![X 1, X 0]
    have hc := congrArg (MvPowerSeries.map f) (FormalGroup.IsComm.comm (F := F))
    rw [map_subst HasSubst.X_X] at hc
    rw [hc]
    congr 1
    funext i
    fin_cases i <;> simp

lemma framed_refl (ρ : R →+* K) (F : FormalGroup R) : FramedEquivalent ρ F F := by
  refine ⟨{
    series := PowerSeries.X
    inverse := PowerSeries.X
    zero_series := by simp
    zero_inverse := by simp
    left_inv := PowerSeries.X_subst _
    right_inv := PowerSeries.X_subst _
    preserves_addition := ?_ },PowerSeries.map_X ρ⟩
  rw [PowerSeries.subst_X (.of_constantCoeff_zero F.zero_constantCoeff),
    PowerSeries.subst_X (PowerSeries.HasSubst.X _),PowerSeries.subst_X (PowerSeries.HasSubst.X _)]
  have hX : ![X 0,X 1]=(X : Fin 2 → MvPowerSeries (Fin 2) R) := by funext i; fin_cases i <;> rfl
  rw [hX,MvPowerSeries.subst_self]; rfl

lemma framed_symm (ρ : R →+* K) {F G : FormalGroup R} (h : FramedEquivalent ρ F G) :
    FramedEquivalent ρ G F := by
  obtain ⟨e,he⟩ := h
  refine ⟨CoordinateTransport.CoordinateIso.symm e,?_⟩
  have hh := (Coordinate.ofIso e).map_eq_of_series_eq ρ Coordinate.ident he
  exact congrArg Coordinate.inverse hh

lemma framed_trans (ρ : R →+* K) {F G H : FormalGroup R}
    (he : FramedEquivalent ρ F G) (hd : FramedEquivalent ρ G H) : FramedEquivalent ρ F H := by
  obtain ⟨e,he⟩ := he
  obtain ⟨d,hd⟩ := hd
  refine ⟨CoordinateTransport.CoordinateIso.trans e d,?_⟩
  change (d.series.subst e.series).map ρ=PowerSeries.X
  have hh : (d.series.subst e.series).map ρ = (d.series.map ρ).subst (e.series.map ρ) :=
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero e.zero_series) d.series
  rw [hh,hd,he,PowerSeries.X_subst]

lemma framed_map (π : R →+* S) (ρ : R →+* K) (σ : S →+* K) (fac : σ.comp π=ρ)
    {F G : FormalGroup R} (he : FramedEquivalent ρ F G) :
    FramedEquivalent σ (F.map π) (G.map π) := by
  obtain ⟨e,he⟩ := he
  refine ⟨CoordinateTransport.CoordinateIso.map e π,?_⟩
  change (e.series.map π).map σ=PowerSeries.X
  rw [unimap_comp,fac,he]

lemma augmentation_of_base_map [Algebra K R] (G : FormalGroup (Base K)) (Γ : FormalGroup K)
    (hG : G.map constantCoeff=Γ) (ρ : R →ₐ[K] K) (f : Base K →ₐ[K] R)
    (hf : ∀ z, ρ (f z)=constantCoeff z) : (G.map f.toRingHom).map ρ.toRingHom=Γ := by
  rw [formal_map_comp,show ρ.toRingHom.comp f.toRingHom=constantCoeff by ext z; exact hf z,hG]

lemma lift_base_map [Algebra K R] [Algebra K S]
    (π : R →ₐ[K] S) (surj : Function.Surjective π) (ρ : R →ₐ[K] K) (σ : S →ₐ[K] K)
    (fac : σ.comp π=ρ) (hnil : ∀ a, ρ a=0 → IsNilpotent a)
    (f : Base K →ₐ[K] S) (hf : ∀ z, σ (f z)=constantCoeff z) :
    ∃ g : Base K →ₐ[K] R, π.comp g=f ∧ (∀ z, ρ (g z)=constantCoeff z) := by
  classical
  let a : Fin 2 → R := fun i => (surj (f (X i))).choose
  have ha (i : Fin 2) : π (a i)=f (X i) := (surj _).choose_spec
  have hρa (i : Fin 2) : ρ (a i)=0 := by
    rw [←fac]; change σ (π (a i))=0
    rw [ha,hf,constantCoeff_X]
  let g : Base K →ₐ[K] R := eval a (fun i => hnil _ (hρa i))
  refine ⟨g,?_,eval_augmentation ρ a _ hρa⟩
  apply hom_ext_nilpotent
  · intro i; simpa [g] using (hnil _ (hρa i)).map π.toRingHom
  · intro i; simp [g,ha]

end HeightThree.ArtinianUniversality

namespace HeightThree.ArtinianUniversality
open MvPowerSeries HondaTarget DeformationRigidity CoordinateTransport NilpotentTower NilpotentEvaluation
variable {K R S : Type*} [Field K] [CommRing R] [CommRing S]

structure Data (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] where
  gamma : FormalGroup K
  family : FormalGroup (Base K)
  family_comm : family.IsComm
  special : family.map constantCoeff=gamma
  honda : multiplicationSeries gamma p=PowerSeries.X^(p^3)
  nonlinear : MvPowerSeries (Fin 2) K
  nonlinear_eq : gamma.toPowerSeries=X 0+X 1+expand (p^2) (pow_ne_zero _ hp.out.ne_zero) nonlinear
  frobenius : gamma.toPowerSeries^p=expand p hp.out.ne_zero gamma.toPowerSeries
  first : (multiplicationSeries family p).coeff p=X 0
  remainder : Base K
  second : (multiplicationSeries family p).coeff (p^2)=X 1+X 0*remainder

namespace Data
variable (p : ℕ) [hp : Fact p.Prime] (D : Data p K)
instance family_isComm : D.family.IsComm := D.family_comm

lemma multiply_coeff_map (F : FormalGroup R) (π : R →+* S) (n j : ℕ) :
    (multiplicationSeries (F.map π) n).coeff j=π ((multiplicationSeries F n).coeff j) := by
  rw [multiplication_map,PowerSeries.coeff_map]

lemma base_gamma [Algebra K R] (ρ : R →ₐ[K] K) :
    (D.gamma.map (algebraMap K R)).map ρ.toRingHom=D.gamma := by
  rw [formal_map_comp]
  apply FormalGroup.ext
  ext d
  change ρ (algebraMap K R (coeff d D.gamma.toPowerSeries))=coeff d D.gamma.toPowerSeries
  simp

lemma gamma_honda [Algebra K R] :
    multiplicationSeries (D.gamma.map (algebraMap K R)) p=PowerSeries.X^(p^3) := by
  rw [multiplication_map,D.honda,map_pow,PowerSeries.map_X]

lemma gamma_nonlinear [Algebra K R] :
    (D.gamma.map (algebraMap K R)).toPowerSeries=X 0+X 1+
      expand (p^2) (pow_ne_zero _ hp.out.ne_zero) (D.nonlinear.map (algebraMap K R)) := by
  change D.gamma.toPowerSeries.map _=_
  rw [D.nonlinear_eq,map_add,map_add,map_X,map_X,map_expand]

lemma gamma_frobenius [Algebra K R] :
    (D.gamma.map (algebraMap K R)).toPowerSeries^p=
      expand p hp.out.ne_zero (D.gamma.map (algebraMap K R)).toPowerSeries := by
  change (D.gamma.toPowerSeries.map _)^p=_
  rw [←map_pow,D.frobenius,map_expand]
  rfl

variable [CharP K p]

lemma lift_step [Algebra K R] [Algebra K S]
    (π : R →ₐ[K] S) (surj : Function.Surjective π) (ρ : R →ₐ[K] K) (σ : S →ₐ[K] K)
    (fac : σ.comp π=ρ) (hsmall : SmallExtension.IsSmall π.toRingHom ρ.toRingHom)
    (hnil : ∀ a, ρ a=0 → IsNilpotent a)
    (F : FormalGroup R) [F.IsComm] (hF : F.map ρ.toRingHom=D.gamma)
    (f : Base K →ₐ[K] S) (hf : ∀ z, σ (f z)=constantCoeff z)
    (he : FramedEquivalent σ.toRingHom (D.family.map f.toRingHom) (F.map π.toRingHom)) :
    ∃ g : Base K →ₐ[K] R, π.comp g=f ∧ (∀ z, ρ (g z)=constantCoeff z) ∧
      FramedEquivalent ρ.toRingHom (D.family.map g.toRingHom) F := by
  have fac' : σ.toRingHom.comp π.toRingHom=ρ.toRingHom := congrArg AlgHom.toRingHom fac
  have : Nontrivial R := ρ.toRingHom.domain_nontrivial
  have : CharP R p := (Algebra.charP_iff K R p).mp inferInstance
  obtain ⟨e,heσ⟩ := framed_symm σ.toRingHom he
  obtain ⟨c,hcπ,hcρ⟩ := Coordinate.lift π.toRingHom surj ρ.toRingHom σ.toRingHom fac' hnil
    (Coordinate.ofIso e) heσ
  let H := c.transport F
  have hHπ : H.map π.toRingHom=D.family.map f.toRingHom := by
    rw [show H=c.transport F from rfl,c.transport_map,hcπ,Coordinate.transport_ofIso]
  have hHρ : H.map ρ.toRingHom=D.gamma := by
    rw [show H=c.transport F from rfl,c.transport_map_eq_self F ρ.toRingHom hcρ,hF]
  obtain ⟨f₀,hf₀π,hf₀ρ⟩ := lift_base_map π surj ρ σ fac hnil f hf
  have hH₀ : H.map π.toRingHom=(D.family.map f₀.toRingHom).map π.toRingHom := by
    rw [formal_map_comp]
    change H.map π.toRingHom=D.family.map (π.comp f₀).toRingHom
    rw [hf₀π,hHπ]
  have hcoeff (j : ℕ) : π ((multiplicationSeries H p).coeff j)=π (f₀ ((multiplicationSeries D.family p).coeff j)) := by
    have hh := congrArg (fun J : FormalGroup S => (multiplicationSeries J p).coeff j) hH₀
    simp only [multiply_coeff_map] at hh
    exact hh
  obtain ⟨g,hgπ,hgρ,hgp,hgpp⟩ := correct_parameters π ρ hsmall.ker_le hsmall.annihilate f₀ hf₀ρ
    (fun i => hnil _ (by rw [hf₀ρ,constantCoeff_X]))
    ((multiplicationSeries D.family p).coeff (p^2)) D.remainder D.second
    ((multiplicationSeries H p).coeff p) ((multiplicationSeries H p).coeff (p^2))
    (by simpa only [D.first] using hcoeff p) (hcoeff (p^2))
  have hgπf : π.comp g=f := hgπ.trans hf₀π
  have hGπ : (D.family.map g.toRingHom).map π.toRingHom=H.map π.toRingHom := by
    rw [formal_map_comp]
    change D.family.map (π.comp g).toRingHom=H.map π.toRingHom
    rw [hgπf,hHπ]
  have hGρ := augmentation_of_base_map D.family D.gamma D.special ρ g hgρ
  obtain ⟨a,haπ⟩ := SmallExtension.small_equivalence_of_matching_parameters p π.toRingHom ρ.toRingHom
    hsmall (D.family.map g.toRingHom) H (D.gamma.map (algebraMap K R)) hGπ
    (hGρ.trans (D.base_gamma p ρ).symm) (hHρ.trans (D.base_gamma p ρ).symm)
    (D.nonlinear.map (algebraMap K R)) (D.gamma_nonlinear p) (D.gamma_honda p) (D.gamma_frobenius p)
    (by rw [multiply_coeff_map,D.first]; exact hgp)
    (by rw [multiply_coeff_map]; exact hgpp)
  have haρ : a.series.map ρ.toRingHom=PowerSeries.X := by
    rw [←fac',←unimap_comp,haπ,PowerSeries.map_X]
  refine ⟨g,hgπf,hgρ,?_⟩
  exact framed_trans ρ.toRingHom ⟨a,haρ⟩ (framed_symm ρ.toRingHom ⟨c.iso F,hcρ⟩)

end Data
end HeightThree.ArtinianUniversality

namespace HeightThree.ArtinianUniversality.Data
open MvPowerSeries HondaTarget DeformationRigidity CoordinateTransport NilpotentTower NilpotentEvaluation
variable {K : Type uK} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (D : Data p K)

lemma existence (n : ℕ) (R : Type uR) [CommRing R] [Algebra K R] (ρ : R →ₐ[K] K)
    (hn : (RingHom.ker ρ)^(n+1)=⊥) (F : FormalGroup R) [F.IsComm]
    (hF : F.map ρ.toRingHom=D.gamma) :
    ∃ g : Base K →ₐ[K] R, (∀ z, ρ (g z)=constantCoeff z) ∧
      FramedEquivalent ρ.toRingHom (D.family.map g.toRingHom) F := by
  induction n generalizing R with
  | zero =>
    let g : Base K →ₐ[K] R := eval (fun _ => 0) (fun _ => IsNilpotent.zero)
    have hg (z : Base K) : ρ (g z)=constantCoeff z := by simp [g,eval_zero]
    have hi : Function.Injective ρ.toRingHom := (RingHom.injective_iff_ker_eq_bot ρ).mpr (by simpa using hn)
    have he : D.family.map g.toRingHom=F := formal_map_injective ρ.toRingHom hi
      ((augmentation_of_base_map D.family D.gamma D.special ρ g hg).trans hF.symm)
    refine ⟨g,hg,?_⟩
    rw [he]
    exact framed_refl ρ.toRingHom F
  | succ n ih =>
    let S := quotient ρ n
    let π : R →ₐ[K] S := projection ρ n
    let σ : S →ₐ[K] K := augmentation ρ n
    have fac : σ.comp π=ρ := rfl
    have hFS : (F.map π.toRingHom).map σ.toRingHom=D.gamma := by
      rw [formal_map_comp]
      exact hF
    obtain ⟨f,hf,he⟩ := ih S σ (augmentation_nilpotent ρ n) (F.map π.toRingHom) hFS
    obtain ⟨g,_,hg,hge⟩ := D.lift_step p π (projection_surjective ρ n) ρ σ fac
      ⟨projection_ker_le ρ n,projection_annihilate ρ n hn⟩
      (fun a ha => nilpotent_of_mem_ker ρ hn ha) F hF f hf he
    exact ⟨g,hg,hge⟩

omit [CharP K p] in
lemma family_honda {R : Type*} [CommRing R] [Algebra K R] (ρ : R →ₐ[K] K)
    (f : Base K →ₐ[K] R) (hf : ∀ z, ρ (f z)=constantCoeff z) :
    (multiplicationSeries (D.family.map f.toRingHom) p).map ρ.toRingHom=PowerSeries.X^(p^3) := by
  rw [←multiplication_map,augmentation_of_base_map D.family D.gamma D.special ρ f hf,D.honda]

end HeightThree.ArtinianUniversality.Data

namespace HeightThree.ArtinianRigidity
open HondaTarget DeformationRigidity CoordinateTransport NilpotentTower

lemma equivalence_rigid {K : Type uK} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (n : ℕ) (R : Type uR) [CommRing R] [Algebra K R] (ρ : R →ₐ[K] K)
    (hn : (RingHom.ker ρ)^(n+1)=⊥) (F G : FormalGroup R) (e : CoordinateIso F G) (hFG : F=G)
    (he : e.series.map ρ.toRingHom=PowerSeries.X)
    (hF : (multiplicationSeries F p).map ρ.toRingHom=PowerSeries.X^(p^3)) :
    e.series=PowerSeries.X := by
  subst G
  exact automorphism_rigid p n R ρ hn F e he hF

end HeightThree.ArtinianRigidity

namespace HeightThree.ArtinianUniversality.Data
open MvPowerSeries HondaTarget DeformationRigidity CoordinateTransport NilpotentTower NilpotentEvaluation
variable {K : Type uK} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (D : Data p K)

lemma base_map_unique (n : ℕ) (R : Type uR) [CommRing R] [Algebra K R] (ρ : R →ₐ[K] K)
    (hn : (RingHom.ker ρ)^(n+1)=⊥) (f g : Base K →ₐ[K] R)
    (hf : ∀ z, ρ (f z)=constantCoeff z) (hg : ∀ z, ρ (g z)=constantCoeff z)
    (he : FramedEquivalent ρ.toRingHom (D.family.map f.toRingHom) (D.family.map g.toRingHom)) : f=g := by
  induction n generalizing R with
  | zero =>
    have hi : Function.Injective ρ := (RingHom.injective_iff_ker_eq_bot ρ).mpr (by simpa using hn)
    ext z
    apply hi
    rw [hf,hg]
  | succ n ih =>
    let S := quotient ρ n
    let π : R →ₐ[K] S := projection ρ n
    let σ : S →ₐ[K] K := augmentation ρ n
    have fac : σ.toRingHom.comp π.toRingHom=ρ.toRingHom := rfl
    have hfS (z : Base K) : σ ((π.comp f) z)=constantCoeff z := hf z
    have hgS (z : Base K) : σ ((π.comp g) z)=constantCoeff z := hg z
    have heS : FramedEquivalent σ.toRingHom (D.family.map (π.comp f).toRingHom)
        (D.family.map (π.comp g).toRingHom) := by
      have hh := framed_map π.toRingHom ρ.toRingHom σ.toRingHom fac he
      rw [formal_map_comp,formal_map_comp] at hh
      exact hh
    have hfg : π.comp f=π.comp g := ih S σ (augmentation_nilpotent ρ n) (π.comp f) (π.comp g) hfS hgS heS
    obtain ⟨e,heρ⟩ := he
    have hFG : (D.family.map f.toRingHom).map π.toRingHom=(D.family.map g.toRingHom).map π.toRingHom := by
      rw [formal_map_comp,formal_map_comp]
      change D.family.map (π.comp f).toRingHom=D.family.map (π.comp g).toRingHom
      rw [hfg]
    let d := CoordinateTransport.CoordinateIso.map e π.toRingHom
    have hd : d.series.map σ.toRingHom=PowerSeries.X := by
      change (e.series.map π.toRingHom).map σ.toRingHom=PowerSeries.X
      rw [unimap_comp,fac,heρ]
    have hF' : (multiplicationSeries ((D.family.map f.toRingHom).map π.toRingHom) p).map σ.toRingHom=PowerSeries.X^(p^3) := by
      rw [formal_map_comp]
      exact D.family_honda p σ (π.comp f) hfS
    have heπ : e.series.map π.toRingHom=PowerSeries.X :=
      ArtinianRigidity.equivalence_rigid p n S σ (augmentation_nilpotent ρ n) _ _ d hFG hd hF'
    have : Nontrivial R := ρ.toRingHom.domain_nontrivial
    have : CharP R p := (Algebra.charP_iff K R p).mp inferInstance
    have hsmall : SmallExtension.IsSmall π.toRingHom ρ.toRingHom :=
      ⟨projection_ker_le ρ n,projection_annihilate ρ n hn⟩
    have hlo (j : ℕ) (hj : 0<j) (hj' : j<p^3) :=
      SmallExtension.small_isomorphism_lowcoeff p π.toRingHom ρ.toRingHom hsmall
        (D.family.map f.toRingHom) (D.family.map g.toRingHom) e heπ
        (D.family_honda p ρ f hf) (D.family_honda p ρ g hg) j hj hj'
    have hx : f (X 0)=g (X 0) := by
      have hh := hlo p hp.out.pos (by simpa only [pow_one] using pow_lt_pow_right₀ hp.out.one_lt (by decide : 1<3))
      rw [multiply_coeff_map,multiply_coeff_map,D.first] at hh
      exact hh
    have hy : f (X 1)=g (X 1) := by
      have hh := hlo (p^2) (pow_pos hp.out.pos _) (pow_lt_pow_right₀ hp.out.one_lt (by decide : 2<3))
      rw [multiply_coeff_map,multiply_coeff_map] at hh
      change f ((multiplicationSeries D.family p).coeff (p^2))=g ((multiplicationSeries D.family p).coeff (p^2)) at hh
      rw [D.second,map_add,map_mul,map_add,map_mul,hx] at hh
      have hk : π (f D.remainder-g D.remainder)=0 := by
        rw [map_sub,sub_eq_zero]
        exact congrArg (fun φ : Base K →ₐ[K] S => φ D.remainder) hfg
      have hr : ρ (g (X 0))=0 := by rw [hg,constantCoeff_X]
      have hz := hsmall.annihilate (f D.remainder-g D.remainder) (g (X 0)) hk hr
      linear_combination hh-hz
    apply hom_ext_nilpotent
    · intro i; exact nilpotent_of_mem_ker ρ hn (by rw [hf,constantCoeff_X])
    · intro i; fin_cases i
      · exact hx
      · exact hy

theorem isUniversal : IsUniversal D.gamma D.family := by
  intro R _ _ _ _ ρ F hFcomm hF
  have := hFcomm
  obtain ⟨n,hn⟩ := finite_local_nilpotent ρ
  obtain ⟨f,hf,he⟩ := D.existence p n R ρ hn F hF
  refine ⟨f,⟨?_,he⟩,?_⟩
  · ext z; exact hf z
  · intro g hg
    apply D.base_map_unique p n R ρ hn g f
    · intro z; exact congrArg (fun φ : Base K →+* K => φ z) hg.1
    · exact hf
    · exact framed_trans ρ.toRingHom hg.2 (framed_symm ρ.toRingHom he)

end HeightThree.ArtinianUniversality.Data

end

end OAI
