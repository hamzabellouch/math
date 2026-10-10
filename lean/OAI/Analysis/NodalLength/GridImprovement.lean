import OAI.Analysis.NodalLength.RegularWeights

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory

namespace SharpNodal.Profiles

abbrev GridIndex (A : ℕ) := Fin 2 → Fin A

def gridCenter (A : ℕ) (p : GridIndex A) : Plane :=
  WithLp.toLp 2 (fun i => ((p i:ℝ)+1/2)/(A:ℝ)-1/2)

def gridCenters (A : ℕ) : Finset Plane := (Finset.univ : Finset (GridIndex A)).image (gridCenter A)

lemma gridCenter_coord {A : ℕ} (hA : 0<A) (p : GridIndex A) (i : Fin 2) :
    |gridCenter A p i|≤1/2 := by
  change |((p i:ℝ)+1/2)/(A:ℝ)-1/2|≤1/2
  have hAr : 0<(A:ℝ) := Nat.cast_pos.mpr hA
  have hp0 : 0≤(p i:ℝ) := Nat.cast_nonneg _
  have hpA : (p i:ℝ)+1≤(A:ℝ) := by exact_mod_cast (p i).isLt
  rw [abs_le]
  constructor
  · have hd : 0≤((p i:ℝ)+1/2)/(A:ℝ) := by positivity
    linarith
  · have hd : ((p i:ℝ)+1/2)/(A:ℝ)≤1 := (div_le_one hAr).mpr (by linarith)
    linarith

lemma gridCenter_norm {A : ℕ} (hA : 0<A) (p : GridIndex A) : ‖gridCenter A p‖≤1 := by
  have h0 := gridCenter_coord hA p 0
  have h1 := gridCenter_coord hA p 1
  have hn := EuclideanSpace.real_norm_sq_eq (gridCenter A p)
  rw [Fin.sum_univ_two] at hn
  have hs0 := pow_le_pow_left₀ (abs_nonneg _) h0 2
  have hs1 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [sq_abs] at hs0 hs1
  nlinarith [norm_nonneg (gridCenter A p)]

lemma fin_real_abs_sub_ge_one {A : ℕ} {p q : Fin A} (hne : p≠q) :
    (1:ℝ)≤|(p:ℝ)-(q:ℝ)| := by
  have hz : ((p:ℕ):ℤ)-((q:ℕ):ℤ)≠0 := by
    intro h
    have h' : (p:ℕ)=(q:ℕ) := by exact_mod_cast sub_eq_zero.mp h
    exact hne (Fin.ext h')
  exact_mod_cast Int.one_le_abs hz

lemma gridCenter_separated {A : ℕ} (hA : 0<A) {p q : GridIndex A} (hne : p≠q) :
    (A:ℝ)⁻¹≤‖gridCenter A p-gridCenter A q‖ := by
  have hAr : 0<(A:ℝ) := Nat.cast_pos.mpr hA
  obtain ⟨i,hi⟩ : ∃i,p i≠q i := Function.ne_iff.mp hne
  have ha := fin_real_abs_sub_ge_one hi
  have hn := plane_component_norm_le (gridCenter A p-gridCenter A q) i
  have he : (gridCenter A p-gridCenter A q) i=((p i:ℝ)-(q i:ℝ))/(A:ℝ) := by
    change (((p i:ℝ)+1/2)/(A:ℝ)-1/2)-(((q i:ℝ)+1/2)/(A:ℝ)-1/2)=_
    ring
  rw [he,abs_div,abs_of_pos hAr] at hn
  have hdiv : (A:ℝ)⁻¹≤|(p i:ℝ)-(q i:ℝ)|/(A:ℝ) := by
    simpa only [one_div] using div_le_div_of_nonneg_right ha hAr.le
  exact hdiv.trans hn

lemma gridCenter_injective {A : ℕ} (hA : 0<A) : Function.Injective (gridCenter A) := by
  intro p q he
  by_contra hne
  have hh := gridCenter_separated hA hne
  rw [he,sub_self,norm_zero] at hh
  exact (not_le_of_gt (inv_pos.mpr (Nat.cast_pos.mpr hA))) hh

lemma gridCenters_card {A : ℕ} (hA : 0<A) : (gridCenters A).card=A^2 := by
  rw [gridCenters,Finset.card_image_of_injective _ (gridCenter_injective hA)]
  simp [GridIndex]

lemma gridCenters_norm {A : ℕ} (hA : 0<A) : ∀y∈gridCenters A,‖y‖≤1 := by
  intro y hy
  obtain ⟨p,_hp,rfl⟩ := Finset.mem_image.mp hy
  exact gridCenter_norm hA p

lemma gridCenters_separated {A : ℕ} (hA : 0<A) :
    ∀y∈gridCenters A,∀y'∈gridCenters A,y≠y' → (A:ℝ)⁻¹≤‖y-y'‖ := by
  intro y hy y' hy' hne
  obtain ⟨p,_hp,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨q,_hq,rfl⟩ := Finset.mem_image.mp hy'
  exact gridCenter_separated hA (fun h =>hne (congrArg (gridCenter A) h))

lemma gridCenters_card_identity {A : ℕ} (hA : 0<A) :
    ((A:ℝ)⁻¹)^2*((gridCenters A).card:ℝ)=1 := by
  rw [gridCenters_card hA,Nat.cast_pow]
  field_simp

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma profile_weighted_sup_real {V : Plane → EReal}
    (hV : UpperSemicontinuousOn V (Metric.ball 0 1000))
    (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    (hanchor : ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a)
    {E : Set Plane} (hE : E⊆Metric.ball (0:Plane) 3) (hpos : volume E≠0)
    {f : Plane → ℝ} {C : ℝ} (hf : ∀x∈E,f x≤C) :
    ∃a : ℝ,(⨆x∈E,V x+(f x:EReal))=(a:EReal) := by
  let a := ⨆x∈E,V x+(f x:EReal)
  have hu : a≤(C:EReal) := by
    refine iSup₂_le (fun x hx => ?_)
    calc
      _ ≤ (0:EReal)+(f x:EReal) := add_le_add (hneg x ((Metric.ball_subset_ball (by norm_num : (3:ℝ)≤1000)) (hE hx))) le_rfl
      _ ≤ _ := by simpa using (EReal.coe_le_coe_iff.mpr (hf x hx))
  have htop : a≠⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top C) hu
  have hae := profile_finite_ae_D3 hV hneg htest hanchor
  obtain ⟨x,hx,hfin⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hae)
  have hfx := hfin (hE hx)
  have hbot : a≠⊥ := by
    have he := EReal.coe_toReal hfx.2 hfx.1
    have hl : (((V x).toReal+f x:ℝ):EReal)≤a := by
      rw [EReal.coe_add,he]
      exact le_iSup₂_of_le x hx le_rfl
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hl
  exact ⟨a.toReal,(EReal.coe_toReal htop hbot).symm⟩

def massExcess (a b : ℝ≥0∞) : ℝ := Real.log (a.toReal/b.toReal)/2

lemma logRate_real {S : ℝ} {m : ℝ≥0∞} (hm0 : m≠0) (hmt : m≠⊤) :
    logRate S m=((Real.log m.toReal/(2*S):ℝ):EReal) := by
  rw [logRate,ENNReal.log_pos_real hm0 hmt,← EReal.coe_mul]
  congr 1
  ring

lemma massExcess_div {S : ℝ} {a b : ℝ≥0∞} (hS : S≠0)
    (ha0 : a≠0) (hat : a≠⊤) (hb0 : b≠0) (hbt : b≠⊤) :
    massExcess a b/S=Real.log a.toReal/(2*S)-Real.log b.toReal/(2*S) := by
  unfold massExcess
  rw [Real.log_div (ENNReal.toReal_ne_zero.mpr ⟨ha0,hat⟩) (ENNReal.toReal_ne_zero.mpr ⟨hb0,hbt⟩)]
  field_simp

lemma eventual_massExcess_bound {S : ℕ → ℝ} (hS : ∀j,0<S j)
    {A B : ℕ → ℝ≥0∞} (hBA : ∀j,B j≤A j) {a e ε : ℝ} (hε : 0<ε)
    (hu : limsup (fun j =>logRate (S j) (A j)) atTop≤((a+e:ℝ):EReal))
    (hl : (a:EReal)≤liminf (fun j =>logRate (S j) (B j)) atTop) :
    ∀ᶠj in atTop,B j≠0 ∧ A j≠⊤ ∧ massExcess (A j) (B j)/S j<e+ε := by
  have huu := eventually_lt_of_limsup_lt (hu.trans_lt (EReal.coe_lt_coe_iff.mpr
    (show a+e<a+e+ε/2 by linarith)))
  have hll := eventually_lt_of_lt_liminf ((EReal.coe_lt_coe_iff.mpr
    (show a-ε/2<a by linarith)).trans_le hl)
  filter_upwards [huu,hll] with j hjh hjl
  have hat : A j≠⊤ := ne_top_of_lt ((logRate_lt_iff (hS j) _).mp hjh)
  have hb0 : B j≠0 := ne_of_gt (lt_trans (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    ((lt_logRate_iff (hS j) _).mp hjl))
  have ha0 : A j≠0 := ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hb0) (hBA j))
  have hbt : B j≠⊤ := ne_top_of_le_ne_top hat (hBA j)
  rw [logRate_real ha0 hat] at hjh
  rw [logRate_real hb0 hbt] at hjl
  have hh := EReal.coe_lt_coe_iff.mp hjh
  have hh' := EReal.coe_lt_coe_iff.mp hjl
  refine ⟨hb0,hat,?_⟩
  rw [massExcess_div (ne_of_gt (hS j)) ha0 hat hb0 hbt]
  linarith

lemma tiltedMass_mono_set (S : ℝ) (B : Plane) (U : Plane → ℝ) (c : ℝ) (f : Plane → ℝ)
    {E F : Set Plane} (hEF : E⊆F) : tiltedMass S B U c f E≤tiltedMass S B U c f F := by
  exact lintegral_mono_set hEF

lemma profile_massExcess_transfer {Ω : Set Plane} {V : Plane → EReal}
    {S c : ℕ → ℝ} {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (hp : WeightedProfileBounds Ω S B U c V) (hS : ∀j,0<S j)
    {f : Plane → ℝ} (hf : ContinuousOn f Ω) {F G E : Set Plane}
    (hF : IsCompact F) (hFΩ : F⊆Ω) (hG : IsOpen G) (hGΩ : G⊆Ω)
    (hGE : G⊆E) (hEF : E⊆F) {a e ε : ℝ} (hε : 0<ε)
    (hinner : (⨆x∈G,V x+(f x:EReal))=(a:EReal))
    (hgap : (⨆x∈F,V x+(f x:EReal))≤((a+e:ℝ):EReal)) :
    ∀ᶠj in atTop,tiltedMass (S j) (B j) (U j) (c j) f G≠0 ∧
      tiltedMass (S j) (B j) (U j) (c j) f E≠⊤ ∧
      massExcess (tiltedMass (S j) (B j) (U j) (c j) f E)
        (tiltedMass (S j) (B j) (U j) (c j) f G)/S j<e+ε := by
  apply eventual_massExcess_bound hS (fun j =>tiltedMass_mono_set _ _ _ _ _ hGE) hε
  · have hm : limsup (fun j =>logRate (S j) (tiltedMass (S j) (B j) (U j) (c j) f E)) atTop≤
        limsup (fun j =>logRate (S j) (tiltedMass (S j) (B j) (U j) (c j) f F)) atTop := by
      exact limsup_le_limsup (Eventually.of_forall (fun j =>logRate_mono (hS j) (tiltedMass_mono_set _ _ _ _ _ hEF)))
    exact hm.trans ((hp.upper f hf F hF hFΩ).trans hgap)
  · rw [← hinner]
    exact hp.lower f hf G hG hGΩ

end SharpNodal.Profiles

noncomputable section
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles

lemma exists_fine_grid (C : ℝ) : ∃A : ℕ,10000<A ∧
    C*((A:ℝ)⁻¹)^2*(1+|Real.log ((A:ℝ)⁻¹)|)<(A:ℝ)⁻¹/4 := by
  have hlog : Tendsto (fun x : ℝ =>Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Tendsto (fun n : ℕ =>(n:ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlogN := hlog.comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ =>(n:ℝ)) atTop atTop)
  have hs : Tendsto (fun n : ℕ =>C*((n:ℝ)⁻¹+Real.log (n:ℝ)/(n:ℝ))) atTop (𝓝 0) := by
    simpa using (hinv.add hlogN).const_mul C
  obtain ⟨A,hA,hc⟩ := ((eventually_gt_atTop (10000:ℕ)).and (hs.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4)))).exists
  refine ⟨A,hA,?_⟩
  have hAr : 0<(A:ℝ) := Nat.cast_pos.mpr (by omega)
  have hAone : 1≤(A:ℝ) := by exact_mod_cast (show 1≤A by omega)
  rw [Real.log_inv,abs_neg,abs_of_nonneg (Real.log_nonneg hAone)]
  have hmul := mul_lt_mul_of_pos_right hc (inv_pos.mpr hAr)
  convert! hmul using 1 <;> field_simp

lemma profile_affine_fixed_grid : ∃A : ℕ,10000<A ∧ ∃Cs : ℝ,0≤Cs ∧
    ∀V : Plane → EReal,UpperSemicontinuousOn V (Metric.ball 0 1000) →
    (∀x∈Metric.ball (0:Plane) 1000,V x≤0) → FullTestProperty (Metric.ball 0 1000) V →
    (∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a) →
    ∃(c : Plane → Plane) (e : Plane → ℝ),
    (∀y∈gridCenters A,0≤e y) ∧
    (∀y∈gridCenters A,(⨆x∈Metric.closedBall y (1000*(A:ℝ)⁻¹),V x-(inner ℝ (c y) (x-y):EReal))≤
      (⨆x∈Metric.ball y ((A:ℝ)⁻¹),V x-(inner ℝ (c y) (x-y):EReal))+(e y:EReal)) ∧
    ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,‖c y‖)≤Cs ∧
    ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,e y)<(A:ℝ)⁻¹/4 := by
  obtain ⟨Cs,Ce,hCs,_hCe,hprof⟩ := affine_profile_grid
  obtain ⟨A,hA,hfine⟩ := exists_fine_grid Ce
  refine ⟨A,hA,Cs,hCs,?_⟩
  intro V hV hneg htest hanchor
  have hApos : 0<A := by omega
  have hAr : 0<(A:ℝ) := Nat.cast_pos.mpr hApos
  have hsmall : 2000*(A:ℝ)⁻¹≤1 := by
    rw [← div_eq_mul_inv,div_le_one hAr]
    exact_mod_cast (show 2000≤A by omega)
  obtain ⟨L,e,he,hbound,hL,heavg⟩ := hprof V hV hneg htest hanchor ((A:ℝ)⁻¹)
    (inv_pos.mpr hAr) hsmall (gridCenters A) (gridCenters_norm hApos)
    (gridCenters_separated hApos) (gridCenters_card_identity hApos)
  let c := fun y => (toDual ℝ Plane).symm (L y)
  have hc (y x : Plane) : inner ℝ (c y) x=L y x := by
    have h := (toDual ℝ Plane).apply_symm_apply (L y)
    exact congrArg (fun f : Plane →L[ℝ] ℝ =>f x) h
  refine ⟨c,e,he,?_,?_,heavg.trans_lt hfine⟩
  · intro y hy
    simpa only [hc] using hbound y hy
  · simpa only [c,LinearIsometryEquiv.norm_map] using hL

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma tiltedMass_const_mul (S : ℝ) (B : Plane) (U : Plane → ℝ) (c d : ℝ)
    (hc : 0≤c) (f : Plane → ℝ) (E : Set Plane) :
    tiltedMass S B U (c*d) f E=ENNReal.ofReal c*tiltedMass S B U d f E := by
  unfold tiltedMass
  simp_rw [mul_assoc,ENNReal.ofReal_mul hc]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma massExcess_mul_left (c a b : ℝ≥0∞) (hc0 : c≠0) (hct : c≠⊤) :
    massExcess (c*a) (c*b)=massExcess a b := by
  unfold massExcess
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,mul_div_mul_left]
  exact ENNReal.toReal_ne_zero.mpr ⟨hc0,hct⟩

lemma tiltedMass_normalized {S : ℝ} {B : Plane} {U : Plane → ℝ} {Ω : Set Plane}
    (hm0 : tiltedMass S B U 1 0 Ω≠0) (hmt : tiltedMass S B U 1 0 Ω≠⊤) :
    let c := (tiltedMass S B U 1 0 Ω).toReal⁻¹
    0<c ∧ tiltedMass S B U c 0 Ω=1 := by
  dsimp only
  have hm : 0<(tiltedMass S B U 1 0 Ω).toReal := ENNReal.toReal_pos hm0 hmt
  refine ⟨inv_pos.mpr hm,?_⟩
  rw [← mul_one (tiltedMass S B U 1 0 Ω).toReal⁻¹,
    tiltedMass_const_mul _ _ _ _ 1 (inv_pos.mpr hm).le,ENNReal.ofReal_inv_of_pos hm,
    ENNReal.ofReal_toReal hmt,ENNReal.inv_mul_cancel hm0 hmt]

lemma normalized_inner_rate {S : ℝ} (hS : 0<S) {B : Plane} {U : Plane → ℝ}
    {Ω G : Set Plane} (hGΩ : G⊆Ω)
    (hm0 : tiltedMass S B U 1 0 G≠0) (hmt : tiltedMass S B U 1 0 Ω≠⊤)
    (hE : massExcess (tiltedMass S B U 1 0 Ω) (tiltedMass S B U 1 0 G)≤S) :
    (-1:EReal)≤logRate S (tiltedMass S B U (tiltedMass S B U 1 0 Ω).toReal⁻¹ 0 G) := by
  let a := tiltedMass S B U 1 0 Ω
  let b := tiltedMass S B U 1 0 G
  have hba : b≤a := tiltedMass_mono_set _ _ _ _ _ hGΩ
  have ha0 : a≠0 := ne_of_gt ((pos_iff_ne_zero.mpr hm0).trans_le hba)
  have hbt : b≠⊤ := ne_top_of_le_ne_top hmt hba
  have ha : 0<a.toReal := ENNReal.toReal_pos ha0 hmt
  have hb : 0<b.toReal := ENNReal.toReal_pos hm0 hbt
  have heq : tiltedMass S B U a.toReal⁻¹ 0 G=ENNReal.ofReal a.toReal⁻¹*b := by
    simpa using tiltedMass_const_mul S B U a.toReal⁻¹ 1 (inv_pos.mpr ha).le 0 G
  have hc0 : ENNReal.ofReal a.toReal⁻¹*b≠0 := mul_ne_zero
    (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ha)) hm0
  have hct : ENNReal.ofReal a.toReal⁻¹*b≠⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbt
  rw [heq,logRate_real hc0 hct,ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_pos.mpr ha).le]
  apply EReal.coe_le_coe_iff.mpr
  have hlog : Real.log (a.toReal⁻¹*b.toReal)= -Real.log (a.toReal/b.toReal) := by
    rw [Real.log_mul (inv_ne_zero (ne_of_gt ha)) (ne_of_gt hb),Real.log_inv,
      Real.log_div (ne_of_gt ha) (ne_of_gt hb)]
    ring
  rw [hlog]
  change Real.log (a.toReal/b.toReal)/2≤S at hE
  rw [le_div_iff₀ (by positivity : (0:ℝ)<2*S)]
  linarith

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma profile_anchor_from_mass {V : Plane → EReal} {S c : ℕ → ℝ}
    {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (hV : UpperSemicontinuousOn V (Metric.ball 0 1000))
    (hp : WeightedProfileBounds (Metric.ball 0 1000) S B U c V)
    (hS : ∀j,0<S j)
    (hinner : ∀j,(-1:EReal)≤logRate (S j)
      (tiltedMass (S j) (B j) (U j) (c j) 0 (Metric.ball 0 1))) :
    ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a := by
  have hsub : Metric.closedBall (0:Plane) 1⊆Metric.ball 0 1000 :=
    Metric.closedBall_subset_ball (by norm_num)
  obtain ⟨a,ha,hmax⟩ := (hV.mono hsub).exists_isMaxOn
    ⟨0,Metric.mem_closedBall_self (by norm_num)⟩ (isCompact_closedBall 0 1)
  refine ⟨a,ha,?_⟩
  have hl : (-1:EReal)≤limsup (fun j =>logRate (S j)
      (tiltedMass (S j) (B j) (U j) (c j) 0 (Metric.closedBall 0 1))) atTop := by
    apply le_limsup_of_frequently_le'
    exact Filter.Eventually.frequently (Eventually.of_forall (fun j => (hinner j).trans
      (logRate_mono (hS j) (tiltedMass_mono_set _ _ _ _ _ Metric.ball_subset_closedBall))))
  have hu := hp.upper 0 continuousOn_const _ (isCompact_closedBall 0 1) hsub
  have hm : (⨆x∈Metric.closedBall (0:Plane) 1,V x+(0:EReal))≤V a := by
    exact iSup₂_le (fun x hx => by simpa using hmax hx)
  exact hl.trans (hu.trans (by simpa using hm))

lemma grid_child_closedBall_subset {A : ℕ} (hA : 10000<A)
    {y : Plane} (hy : y∈gridCenters A) :
    Metric.closedBall y (1000*(A:ℝ)⁻¹)⊆Metric.ball (0:Plane) 3 := by
  have hAr : 0<(A:ℝ) := Nat.cast_pos.mpr (by omega)
  have hr : 1000*(A:ℝ)⁻¹<1 := by
    rw [← div_eq_mul_inv,div_lt_one hAr]
    exact_mod_cast (show 1000<A by omega)
  intro x hx
  rw [Metric.mem_ball,dist_zero_right]
  have hd : ‖x-y‖≤1000*(A:ℝ)⁻¹ := by simpa [dist_eq_norm] using hx
  have hn := gridCenters_norm (by omega : 0<A) y hy
  have ht : ‖x‖≤‖x-y‖+‖y‖ := by simpa using norm_add_le (x-y) y
  linarith

lemma tilted_grid_averaged_transfer {A : ℕ} (hA : 10000<A)
    {V : Plane → EReal} {S d : ℕ → ℝ} {B : ℕ → Plane} {U : ℕ → Plane → ℝ}
    (hV : UpperSemicontinuousOn V (Metric.ball 0 1000))
    (hneg : ∀x∈Metric.ball (0:Plane) 1000,V x≤0)
    (htest : FullTestProperty (Metric.ball 0 1000) V)
    (hanchor : ∃a∈Metric.closedBall (0:Plane) 1,(-1:EReal)≤V a)
    (hp : WeightedProfileBounds (Metric.ball 0 1000) S B U d V)
    (hS : ∀j,0<S j) {c : Plane → Plane} {e : Plane → ℝ}
    (hgap : ∀y∈gridCenters A,
      (⨆x∈Metric.closedBall y (1000*(A:ℝ)⁻¹),V x-(inner ℝ (c y) (x-y):EReal))≤
      (⨆x∈Metric.ball y ((A:ℝ)⁻¹),V x-(inner ℝ (c y) (x-y):EReal))+(e y:EReal))
    (he : ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,e y)<(A:ℝ)⁻¹/4) :
    ∀ᶠj in atTop,
      (∀y∈gridCenters A,tiltedMass (S j) (B j) (U j) (d j)
        (fun x => -inner ℝ (c y) (x-y)) (Metric.ball y ((A:ℝ)⁻¹))≠0 ∧
        tiltedMass (S j) (B j) (U j) (d j)
          (fun x => -inner ℝ (c y) (x-y)) (Metric.ball y (1000*(A:ℝ)⁻¹))≠⊤) ∧
      ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,
        massExcess (tiltedMass (S j) (B j) (U j) (d j) (fun x => -inner ℝ (c y) (x-y))
            (Metric.ball y (1000*(A:ℝ)⁻¹)))
          (tiltedMass (S j) (B j) (U j) (d j) (fun x => -inner ℝ (c y) (x-y))
            (Metric.ball y ((A:ℝ)⁻¹)))/S j)<(A:ℝ)⁻¹/2 := by
  let ρ : ℝ := (A:ℝ)⁻¹
  have hρ : 0<ρ := inv_pos.mpr (Nat.cast_pos.mpr (by omega : 0<A))
  have hρR : ρ≤1000*ρ := by linarith
  have hc (y : Plane) : Continuous (fun x => -inner ℝ (c y) (x-y)) :=
    (continuous_const.inner (continuous_id.sub continuous_const)).neg
  have hall : ∀ᶠj in atTop,∀y∈gridCenters A,
      tiltedMass (S j) (B j) (U j) (d j) (fun x => -inner ℝ (c y) (x-y)) (Metric.ball y ρ)≠0 ∧
      tiltedMass (S j) (B j) (U j) (d j) (fun x => -inner ℝ (c y) (x-y)) (Metric.ball y (1000*ρ))≠⊤ ∧
      massExcess (tiltedMass (S j) (B j) (U j) (d j) (fun x => -inner ℝ (c y) (x-y)) (Metric.ball y (1000*ρ)))
        (tiltedMass (S j) (B j) (U j) (d j) (fun x => -inner ℝ (c y) (x-y)) (Metric.ball y ρ))/S j<e y+ρ/8 := by
    apply (eventually_all_finset (gridCenters A)).mpr
    intro y hy
    have hF3 := grid_child_closedBall_subset hA hy
    have hG3 := (Metric.ball_subset_ball hρR |>.trans Metric.ball_subset_closedBall).trans hF3
    have h3R : Metric.ball (0:Plane) 3⊆Metric.ball 0 1000 := Metric.ball_subset_ball (by norm_num)
    have hfbd : ∀x∈Metric.ball y ρ,-inner ℝ (c y) (x-y)≤‖c y‖*ρ := by
      intro x hx
      have hh : ‖x-y‖<ρ := by simpa [dist_eq_norm] using hx
      calc
        _ ≤ |inner ℝ (c y) (x-y)| := neg_le_abs _
        _ ≤ ‖c y‖*‖x-y‖ := abs_real_inner_le_norm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hh.le (norm_nonneg _)
    obtain ⟨a,ha⟩ := profile_weighted_sup_real hV hneg htest hanchor hG3
      (ne_of_gt (Metric.measure_ball_pos volume y hρ)) hfbd
    apply profile_massExcess_transfer hp hS (hc y).continuousOn
      (isCompact_closedBall y (1000*ρ)) (hF3.trans h3R) Metric.isOpen_ball (hG3.trans h3R)
      (Metric.ball_subset_ball hρR) Metric.ball_subset_closedBall (by positivity : (0:ℝ)<ρ/8) ha
    have ha' : (⨆x∈Metric.ball y ρ,V x-(inner ℝ (c y) (x-y):EReal))=(a:EReal) := by
      simpa only [EReal.coe_neg,← sub_eq_add_neg] using ha
    simpa only [ρ,ha',← EReal.coe_add,EReal.coe_neg,← sub_eq_add_neg] using hgap y hy
  filter_upwards [hall] with j hj
  refine ⟨fun y hy => ⟨(hj y hy).1,(hj y hy).2.1⟩,?_⟩
  have hs := Finset.sum_le_sum (fun y hy => (hj y hy).2.2.le)
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg ρ)
  have hi : ρ^2*(∑y∈gridCenters A,(e y+ρ/8))=
      ρ^2*(∑y∈gridCenters A,e y)+ρ/8 := by
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_add,← mul_assoc]
    have hid : ρ^2*(gridCenters A).card=1 := gridCenters_card_identity (by omega : 0<A)
    rw [hid,one_mul]
  rw [hi] at hm
  change ρ^2*(∑y∈gridCenters A,e y)<ρ/4 at he
  exact lt_of_le_of_lt hm (by linarith)

def gridExcess (A : ℕ) (S : ℝ) (B : Plane) (U : Plane → ℝ) (d : ℝ)
    (c : Plane → Plane) (y : Plane) : ℝ :=
  massExcess (tiltedMass S B U d (fun x => -inner ℝ (c y) (x-y))
      (Metric.ball y (1000*(A:ℝ)⁻¹)))
    (tiltedMass S B U d (fun x => -inner ℝ (c y) (x-y))
      (Metric.ball y ((A:ℝ)⁻¹)))

def gridMassesFinite (A : ℕ) (S : ℝ) (B : Plane) (U : Plane → ℝ) (d : ℝ)
    (c : Plane → Plane) : Prop :=
  ∀y∈gridCenters A,tiltedMass S B U d (fun x => -inner ℝ (c y) (x-y))
    (Metric.ball y ((A:ℝ)⁻¹))≠0 ∧
    tiltedMass S B U d (fun x => -inner ℝ (c y) (x-y))
      (Metric.ball y (1000*(A:ℝ)⁻¹))≠⊤

theorem sequence_affine_improvement : ∃A : ℕ,10000<A ∧ ∃Cs : ℝ,0≤Cs ∧
    ∀(p U : ℕ → Plane → ℝ) (B : ℕ → Plane) (S K e d : ℕ → ℝ) (Cp : ℝ),
    (∀j,ContDiffOn ℝ ∞ (p j) (Metric.ball 0 1000)) →
    (∀j,ContDiffOn ℝ ∞ (U j) (Metric.ball 0 1000)) →
    (∀j,0<S j) → Tendsto S atTop atTop → (∀j,0<d j) →
    Tendsto (fun j =>K j/(S j+‖B j‖)) atTop (𝓝 0) →
    (∀j x,x∈Metric.ball (0:Plane) 1000 → |p j x|≤Cp) →
    Tendsto e atTop (𝓝 0) →
    (∀j i x,x∈Metric.ball (0:Plane) 1000 →
      |(K j)^2*coordPartial (p j) i x/(S j*(S j+‖B j‖))|≤e j) →
    (∀j x,x∈Metric.ball (0:Plane) 1000 →
      euclideanLaplacian (U j) x+(K j)^2*p j x*U j x=0) →
    (∀j,tiltedMass (S j) (B j) (U j) (d j) 0 (Metric.ball 0 1000)≤1) →
    (∀j,(-1:EReal)≤logRate (S j)
      (tiltedMass (S j) (B j) (U j) (d j) 0 (Metric.ball 0 1))) →
    ∃(φ : ℕ → ℕ) (c : Plane → Plane),StrictMono φ ∧
      ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,‖c y‖)≤Cs ∧
      ∀ᶠj in atTop,gridMassesFinite A (S (φ j)) (B (φ j)) (U (φ j)) (d (φ j)) c ∧
      ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,
        gridExcess A (S (φ j)) (B (φ j)) (U (φ j)) (d (φ j)) c y/S (φ j))<(A:ℝ)⁻¹/2 := by
  obtain ⟨A,hA,Cs,hCs,hgrid⟩ := profile_affine_fixed_grid
  refine ⟨A,hA,Cs,hCs,?_⟩
  intro p U B S K e d Cp hp hU hSpos hS hd hK hpbound he hpgrad hPDE hnorm hinner
  obtain ⟨V,φ,hφ,hV,hneg,hprof⟩ := extract_tilted_profile Metric.isOpen_ball S B U d
    hSpos hS (fun j =>(hU j).continuousOn) hnorm
  have htest := full_test_of_profile Metric.isOpen_ball (fun j =>hp (φ j))
    (fun j =>hU (φ j)) (fun j =>hSpos (φ j)) (hS.comp hφ.tendsto_atTop)
    (fun j =>hd (φ j)) (hK.comp hφ.tendsto_atTop) (fun j =>hpbound (φ j))
    (he.comp hφ.tendsto_atTop) (fun j =>hpgrad (φ j)) (fun j =>hPDE (φ j))
    (hV.upperSemicontinuousOn _) hprof
  have hanchor := profile_anchor_from_mass (hV.upperSemicontinuousOn _) hprof
    (fun j =>hSpos (φ j)) (fun j =>hinner (φ j))
  obtain ⟨c,err,_herr,hgap,hc,havg⟩ := hgrid V (hV.upperSemicontinuousOn _)
    (fun x _ =>hneg x) htest hanchor
  refine ⟨φ,c,hφ,hc,?_⟩
  filter_upwards [tilted_grid_averaged_transfer hA (hV.upperSemicontinuousOn _)
    (fun x _ =>hneg x) htest hanchor hprof (fun j =>hSpos (φ j)) hgap havg] with j hj
  exact hj

end SharpNodal.Profiles

end
end
end
end
end

end OAI
