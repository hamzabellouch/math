import OAI.NumberTheory.DirichletL.Moments.ReflectedChoiceEnergy
import OAI.NumberTheory.DirichletL.Moments.UniformReflectionApproximation
import OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow
import OAI.NumberTheory.DirichletL.Energy.ReferenceDivisors

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroReflectionSupport
open HeckeFamily Filter CenteredMomentNaturalPrimitive EisensteinSchwartzPoisson
open CenteredMomentReflectionMass CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentReflectionDeletion CenteredMomentReflectionWeightedEnergy
open CenteredMomentReflectedChoiceEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentUniformReflectionApproximation
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDivisors CenteredMomentEnergyReferenceLowWindow
open CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O" => HeckeFamily.O

def naturalDualScale (χ ψ : Character) (X : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) : ℝ :=
  (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)

lemma naturalDualScale_pos (χ ψ : Character) (X : ℝ) (hX : 0<X)
    (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
    (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) :
    0<naturalDualScale χ ψ X D H := by
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hN := subset_product_norm_pos D (fun P hP=>redundantSet_prime _ _ P
    (Finset.mem_powerset.mp hD hP))
  have hH := norm_pos H.val
  unfold naturalDualScale
  positivity

theorem eventually_natural_choice_range (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M →
      ∀(D : Finset (Ideal O))(_hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
        (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0<naturalDualScale χ ψ (Z^a) D H)(n : ℤ),
      n∈retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY → 0≤M-a+xi := by
  filter_upwards [eventually_natural_choice_geometry C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod D hD H hY n hn
  have h := hZ.2 χ ψ M a hcap hmod ((⟨D,hD⟩,H),n) hY hn
  have hz := Real.log_pos hZ.1
  have hm : 0≤(M-a+xi)*Real.log Z := h.2.1.trans h.2.2
  nlinarith

theorem eventually_natural_source_zero (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M → M+xi<a →
      (∀(D : Finset (Ideal O))(_hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
        (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0<naturalDualScale χ ψ (Z^a) D H),
        retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY=∅) ∧
      (∀(D : Finset (Ideal O)),D∈(redundantSet χ.modulus ψ.modulus).powerset →
        ∀(H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))(η : Character)(F : ℝ→ℂ),
        finiteAnnularColumn η F (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H)=0) ∧
      (∀(W : ℝ→ℂ)(t : ℝ),retainedOriginal χ ψ W (Z^a) (Z^(xi/4)) t=0) ∧
      (∀G : 𝓢(ℝ,ℂ),retainedSchwartz χ ψ G (Z^a) (Z^(xi/4))=0) := by
  filter_upwards [eventually_natural_choice_range C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod hfar
  have hempty (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
      (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
      (hY : 0<naturalDualScale χ ψ (Z^a) D H) :
      retainedAnnuli (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H) hY=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro n hn
    have h := hZ.2 χ ψ M a hcap hmod D hD H hY n hn
    linarith
  have hcol (D : Finset (Ideal O)) (hD : D∈(redundantSet χ.modulus ψ.modulus).powerset)
      (H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)) (η : Character)(F : ℝ→ℂ) :
      finiteAnnularColumn η F (Z^(xi/4)) (naturalDualScale χ ψ (Z^a) D H)=0 := by
    have hy := naturalDualScale_pos χ ψ (Z^a) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) D hD H
    rw [finiteAnnularColumn,dite_eq_left hy,hempty D hD H hy]
    simp
  refine ⟨hempty,hcol,?_,?_⟩
  · intro W t
    unfold retainedOriginal
    apply Finset.sum_eq_zero
    intro D hD
    have hz : (fun H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)=>
        coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
        finiteAnnularColumn χ.inverse
          (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Z^(xi/4))
          (naturalDualScale χ ψ (Z^a) D H))=fun _=>0 := by
      funext H
      rw [hcol D hD H]
      simp
    change (∑'H : SmoothIdeal (redundantSet χ.modulus ψ.modulus),
      coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
      finiteAnnularColumn χ.inverse
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Z^(xi/4))
        (naturalDualScale χ ψ (Z^a) D H))=0
    rw [hz,tsum_zero]
  · intro G
    unfold retainedSchwartz
    apply Finset.sum_eq_zero
    intro D hD
    have hz : (fun H : SmoothIdeal (redundantSet χ.modulus ψ.modulus)=>
        coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
        finiteAnnularColumn χ.inverse (paperRadialFourier G) (Z^(xi/4))
          (naturalDualScale χ ψ (Z^a) D H))=fun _=>0 := by
      funext H
      rw [hcol D hD H]
      simp
    change (∑'H : SmoothIdeal (redundantSet χ.modulus ψ.modulus),
      coefficient ψ ψ.inverse (redundantSet χ.modulus ψ.modulus) D H*
      finiteAnnularColumn χ.inverse (paperRadialFourier G) (Z^(xi/4))
        (naturalDualScale χ ψ (Z^a) D H))=0
    rw [hz,tsum_zero]

lemma deleted_short_length (Z b Xshort Xlong Nshort : ℝ)
    (hZ : 1<Z)(_hb : 0<b)(hshort : 0<Xshort)(hlong : Xshort≤Xlong)
    (hN : 1≤Nshort)(hsupport : 1≤b*Xlong) :
    length Z (Xshort/Nshort)≤Real.logb Z Xlong+Real.logb Z (max 1 b) := by
  have hx : 0<Xlong := hshort.trans_le hlong
  have hn : 0<Nshort := zero_lt_one.trans_le hN
  have hd : Xshort/Nshort≤Xlong := (div_le_self hshort.le hN).trans hlong
  have hlog := Real.logb_le_logb_of_le hZ (div_pos hshort hn) hd
  have hprod : 1≤max 1 b*Xlong := hsupport.trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hx.le)
  have hzero := Real.logb_nonneg hZ hprod
  rw [Real.logb_mul (ne_of_gt (zero_lt_one.trans_le (le_max_left 1 b))) hx.ne'] at hzero
  rw [length_eq_max_log Z _ hZ (div_pos hshort hn)]
  apply max_le
  · linarith
  · exact hlog.trans (le_add_of_nonneg_right (Real.logb_nonneg hZ (le_max_left _ _)))

theorem live_deleted_growth (Z b M xi Xshort Xlong Nshort Nlong : ℝ)
    (hZ : 1<Z)(hb : 0<b)(_hM : 0≤M)(hshort : 0<Xshort)(hlong : Xshort≤Xlong)
    (hNs : 1≤Nshort)(hNl : 1≤Nlong)(hsupport : 1≤b*Xlong)
    (hlive : 0≤M-Real.logb Z (Xlong/Nlong)+xi)
    (x : ℝ)(hx : x∈Set.Icc 0 (max 0 (M-Real.logb Z (Xlong/Nlong)+xi)*Real.log Z)) :
    length Z (Real.exp x)+length Z (Xshort/Nshort)≤
      M+Real.logb Z Nlong+Real.logb Z (max 1 b)+xi := by
  have hxlong : 0<Xlong := hshort.trans_le hlong
  have hnlong : 0<Nlong := zero_lt_one.trans_le hNl
  have hwindow := (reflection_window_length Z _ x hZ (le_max_left _ _) hx).1
  rw [max_eq_right hlive,Real.logb_div hxlong.ne' hnlong.ne'] at hwindow
  have hshortbound := deleted_short_length Z b Xshort Xlong Nshort hZ hb hshort hlong hNs hsupport
  linarith

theorem eventually_endpoint_defect (b epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ Real.logb Z (max 1 b)≤epsilon := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log (max 1 b)/epsilon))] with Z hZ hz
  refine ⟨hZ,?_⟩
  rw [Real.logb]
  apply (div_le_iff₀ (Real.log_pos hZ)).mpr
  have hh := (div_le_iff₀ hepsilon).mp hz
  nlinarith

theorem actual_deleted_growth {Z Bmask bΦ : ℝ}(s : NaturalState Z Bmask bΦ)
    (b xi Xshort Xlong : ℝ)(hZ : 1<Z)(hb : 0<b)
    (hshort : 0<Xshort)(hlong : Xshort≤Xlong)(hsupport : 1≤b*Xlong)
    (Dshort Dlong : Finset (Ideal O))
    (hDs : Dshort∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hDl : Dlong∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hlive : 0≤s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)
    (x : ℝ)(hx : x∈Set.Icc 0
      (max 0 (s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z)) :
    length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
      s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+Real.logb Z (max 1 b)+xi := by
  exact live_deleted_growth Z b s.width xi Xshort Xlong _ _ hZ hb s.width_nonneg
    hshort hlong (divisor_norm s Dshort hDs).1 (divisor_norm s Dlong hDl).1 hsupport hlive x hx

theorem eventually_actual_source_zero (bΦ xi : ℝ)(hbΦ : 0<bΦ)(hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(Bmask : ℝ)(s : NaturalState Z Bmask bΦ)
      (z : O),(effectiveState s).radial.keep z →
      let χ := naturalCharacter s.character z
      ∀ψ : Character,
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      ∀a : ℝ,s.width+xi<a →
      (∀(W : ℝ→ℂ)(t : ℝ),retainedOriginal χ ψ W (Z^a) (Z^(xi/4)) t=0) ∧
      (∀G : 𝓢(ℝ,ℂ),retainedSchwartz χ ψ G (Z^a) (Z^(xi/4))=0) := by
  let C : ℝ := ((fixedConductorFactor:ℝ)+1)*bΦ
  have hC : 0<C := mul_pos (by positivity) hbΦ
  filter_upwards [eventually_natural_source_zero C xi hC hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask s z hz
  dsimp only
  intro ψ hcap a hfar
  have hm : ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤C*Z^s.width := by
    apply (effective_character_cap s hbΦ.le z hz).trans
    dsimp only [C]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hbΦ.le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  exact (hZ.2 (naturalCharacter s.character z) ψ s.width a hcap hm hfar).2.2

theorem eventually_actual_deleted_growth (b epsilon : ℝ)(hb : 0<b)(hepsilon : 0<epsilon) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(Bmask bΦ : ℝ)(s : NaturalState Z Bmask bΦ)
      (xi Xshort Xlong : ℝ),0<Xshort → Xshort≤Xlong → 1≤b*Xlong →
      ∀(Dshort Dlong : Finset (Ideal O)),
      Dshort∈(CompletedGauss.primeSupport s.puncture).powerset →
      Dlong∈(CompletedGauss.primeSupport s.puncture).powerset →
      0≤s.width-Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi →
      ∀x∈Set.Icc 0 (max 0 (s.width-Real.logb Z
        (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z),
      length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
        s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+epsilon+xi := by
  filter_upwards [eventually_endpoint_defect b epsilon hepsilon] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Bmask bΦ s xi Xshort Xlong hshort hlong hsupport Dshort Dlong hDs hDl hlive x hx
  have h := actual_deleted_growth s b xi Xshort Xlong hZ.1 hb hshort hlong hsupport
    Dshort Dlong hDs hDl hlive x hx
  linarith [hZ.2]

theorem eventually_actual_retained_deleted_growth (b bΦ xi epsilon : ℝ)
    (hb : 0<b)(hbΦ : 0<bΦ)(hxi : 0<xi)(hepsilon : 0<epsilon) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(Bmask : ℝ)(s : NaturalState Z Bmask bΦ)
      (z : O),(effectiveState s).radial.keep z →
      let χ := naturalCharacter s.character z
      ∀ψ : Character,
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      ∀(Xshort Xlong : ℝ),0<Xshort → Xshort≤Xlong → 1≤b*Xlong →
      ∀(Dshort Dlong : Finset (Ideal O)),
      Dshort∈(CompletedGauss.primeSupport s.puncture).powerset →
      Dlong∈(CompletedGauss.primeSupport s.puncture).powerset →
      ∀(E : Finset (Ideal O)),E∈(redundantSet χ.modulus ψ.modulus).powerset →
      ∀(H : SmoothIdeal (redundantSet χ.modulus ψ.modulus))
        (hY : 0<naturalDualScale χ ψ (Xlong/((∏P∈Dlong,P).absNorm:ℝ)) E H)(n : ℤ),
      n∈retainedAnnuli (Z^(xi/4))
        (naturalDualScale χ ψ (Xlong/((∏P∈Dlong,P).absNorm:ℝ)) E H) hY →
      ∀x∈Set.Icc 0 (max 0 (s.width-Real.logb Z
        (Xlong/((∏P∈Dlong,P).absNorm:ℝ))+xi)*Real.log Z),
      length Z (Real.exp x)+length Z (Xshort/((∏P∈Dshort,P).absNorm:ℝ))≤
        s.width+Real.logb Z ((∏P∈Dlong,P).absNorm:ℝ)+epsilon+xi := by
  let C : ℝ := ((fixedConductorFactor:ℝ)+1)*bΦ
  have hC : 0<C := mul_pos (by positivity) hbΦ
  filter_upwards [eventually_natural_choice_range C xi hC hxi,
    eventually_actual_deleted_growth b epsilon hb hepsilon] with Z hZ hgrowth
  refine ⟨hZ.1,?_⟩
  intro Bmask s z hz
  dsimp only
  intro ψ hcap Xshort Xlong hshort hlong hsupport Dshort Dlong hDs hDl E hE H hY n hn x hx
  have hm : ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤C*Z^s.width := by
    apply (effective_character_cap s hbΦ.le z hz).trans
    dsimp only [C]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hbΦ.le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
  have hL : 0<Xlong/((∏P∈Dlong,P).absNorm:ℝ) :=
    div_pos (hshort.trans_le hlong) (zero_lt_one.trans_le (divisor_norm s Dlong hDl).1)
  have hexp : Z^(Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ)))=
      Xlong/((∏P∈Dlong,P).absNorm:ℝ) :=
    Real.rpow_logb (zero_lt_one.trans hZ.1) hZ.1.ne' hL
  have hrange := hZ.2 (naturalCharacter s.character z) ψ s.width
    (Real.logb Z (Xlong/((∏P∈Dlong,P).absNorm:ℝ))) hcap hm E hE H
  rw [hexp] at hrange
  have hlive := hrange hY n hn
  exact hgrowth.2 Bmask bΦ s xi Xshort Xlong hshort hlong hsupport
    Dshort Dlong hDs hDl hlive x hx

end SevenEighths.CenteredMomentEnergyZeroReflectionSupport

end

end OAI
