import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.QuadraticRectangleCounts
import OAI.GroupTheory.SimpleAmenable.Arithmetic.QuadraticTiles

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section LatticeRiemann
open Classical MeasureTheory

theorem fundamentalDomain_riemann_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddLeftInvariant (volume : Measure E)]
    (L : AddSubgroup E) [Countable L]
    {F : Set E} (hF : IsAddFundamentalDomain L F volume)
    (hFfin : volume F<⊤) {δ : ℝ} (hδ : ∀x∈F,‖x‖≤δ)
    {f : E → ℝ} (hf : Integrable f) {A : NNReal} (hlip : LipschitzWith A f)
    (T : Finset L) (hT : ∀z : L,z∉T → ∀x∈F,f ((z:E)+x)=0) :
    |volume.real F*(∑z∈T,f (z:E))-∫x,f x| ≤
      (T.card:ℝ)*((A:ℝ)*δ*volume.real F) := by
  have hint (z : L) : Integrable (fun x : E => f ((z:E)+x)) :=
    (measurePreserving_add_left volume (z:E)).integrable_comp_of_integrable hf
  have hdecomp : (∫x,f x)=∑z∈T,∫x in F,f ((z:E)+x) := by
    rw [hF.integral_eq_tsum'' f hf]
    apply tsum_eq_sum
    intro z hz
    apply integral_eq_zero_of_ae
    exact (ae_restrict_mem₀ hF.nullMeasurableSet).mono (fun x hx => hT z hz x hx)
  rw [hdecomp,Finset.mul_sum,← Finset.sum_sub_distrib]
  have he (z : L) : volume.real F*f (z:E)-(∫x in F,f ((z:E)+x))=
      ∫x in F,f (z:E)-f ((z:E)+x) := by
    rw [integral_sub (integrableOn_const (C := f (z:E)) hFfin.ne) (hint z).integrableOn,
      setIntegral_const,smul_eq_mul]
  simp_rw [he]
  calc
    _ ≤ ∑z∈T,|∫x in F,f (z:E)-f ((z:E)+x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_z∈T,(A:ℝ)*δ*volume.real F := by
      apply Finset.sum_le_sum
      intro z _
      rw [← Real.norm_eq_abs]
      apply norm_setIntegral_le_of_norm_le_const hFfin
      intro x hx
      calc
        _ ≤ (A:ℝ)*‖(z:E)-((z:E)+x)‖ := hlip.norm_sub_le _ _
        _ = (A:ℝ)*‖x‖ := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hδ x hx) A.coe_nonneg
    _ = _ := by simp

end LatticeRiemann

section PairedQuadraticTiles
open Classical Module MeasureTheory

theorem balanced_cutUnit_pos {L : ℝ} (hL : 0<L) :
    ∃u : CutRing,IsUnit u ∧ |ordinary u| ≤ 2/L ∧ |conjugate u| ≤ 2*L := by
  by_cases hh : 1≤L
  · obtain ⟨u,hu,ho,hc⟩ := balanced_cutUnit hh
    exact ⟨u,hu,ho,hc.trans (by linarith)⟩
  · have hLi : 1≤L⁻¹ := (one_le_inv₀ hL).mpr (le_of_not_ge hh)
    obtain ⟨u,hu,ho,hc⟩ := balanced_cutUnit hLi
    obtain ⟨U,rfl⟩ := hu
    have heo : |ordinary (↑(U⁻¹):CutRing)| * |ordinary (↑U:CutRing)|=1 := by
      rw [← abs_mul,← map_mul]; simp
    have hec : |conjugate (↑(U⁻¹):CutRing)| * |conjugate (↑U:CutRing)|=1 := by
      rw [← abs_mul,← map_mul]; simp
    have hn := cutUnit_abs_norm U.isUnit
    rw [abs_mul] at hn
    have ho₀ : 0 < |ordinary (↑U:CutRing)| := by
      exact lt_of_le_of_ne (abs_nonneg _) (by intro hh; rw [← hh,zero_mul] at hn; norm_num at hn)
    have hc₀ : 0 < |conjugate (↑U:CutRing)| := by
      exact lt_of_le_of_ne (abs_nonneg _) (by intro hh; rw [← hh,mul_zero] at hn; norm_num at hn)
    refine ⟨(↑(U⁻¹):CutRing),(U⁻¹).isUnit,?_,?_⟩
    · have he : |ordinary (↑(U⁻¹):CutRing)|=|conjugate (↑U:CutRing)| := by nlinarith
      rw [he]
      exact hc.trans (by rw [div_eq_mul_inv]; have := inv_pos.mpr hL; linarith)
    · have he : |conjugate (↑(U⁻¹):CutRing)|=|ordinary (↑U:CutRing)| := by nlinarith
      rw [he]
      simpa only [div_inv_eq_mul] using ho

theorem quadraticSmallTile {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) :
    ∃u : CutRing,∃hu : IsUnit u,∀x∈ZSpan.fundamentalDomain (quadraticScaledBasis hu hd hs ht),
      ‖x‖ ≤ 6/(d*Real.sqrt (s*t)) := by
  let L := Real.sqrt (t/s)
  have hL : 0<L := Real.sqrt_pos.2 (div_pos ht hs)
  obtain ⟨u,hu,ho,hc⟩ := balanced_cutUnit_pos hL
  have hsq : L^2=t/s := Real.sq_sqrt (div_nonneg ht.le hs.le)
  have hsq' : L^2*s=t := (eq_div_iff hs.ne').mp hsq
  have hmul : L*s=Real.sqrt (s*t) := by
    have he : (L*s)^2=s*t := by nlinarith
    nlinarith [Real.sq_sqrt (mul_pos hs ht).le,Real.sqrt_nonneg (s*t),mul_pos hL hs]
  have hdiv : L/t=(Real.sqrt (s*t))⁻¹ := by
    rw [← hmul]
    apply (div_eq_iff ht.ne').mpr
    field_simp
    nlinarith [hsq']
  refine ⟨u,hu,fun x hx => ?_⟩
  have hb := quadraticScaledTile_bound hu hd hs ht x hx
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · rw [Real.norm_eq_abs]
    calc
      _ ≤ 3*|ordinary u|/(d*s) := hb.1
      _ ≤ 3*(2/L)/(d*s) := by gcongr
      _ = 6/(d*Real.sqrt (s*t)) := by rw [← hmul]; field_simp; ring
  · rw [Real.norm_eq_abs]
    calc
      _ ≤ 2*|conjugate u|/(d*t) := hb.2
      _ ≤ 2*(2*L)/(d*t) := by gcongr
      _ = 4/(d*Real.sqrt (s*t)) := by
        calc
          _ = (4/d)*(L/t) := by ring
          _ = _ := by rw [hdiv]; ring
      _ ≤ _ := by gcongr; norm_num

noncomputable def pairedQuadraticBasis {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) :
    Basis (Fin 2 ⊕ Fin 2) ℝ ((Fin 2 → ℝ)×(Fin 2 → ℝ)) :=
  (quadraticScaledBasis hu hd hs ht).prod (quadraticScaledBasis hu hd hs ht)

theorem pairedQuadraticDomain {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) :
    ZSpan.fundamentalDomain (pairedQuadraticBasis hu hd hs ht)=
      (ZSpan.fundamentalDomain (quadraticScaledBasis hu hd hs ht)) ×ˢ
      (ZSpan.fundamentalDomain (quadraticScaledBasis hu hd hs ht)) := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain,pairedQuadraticBasis,Sum.forall,
    Basis.prod_repr_inl,Basis.prod_repr_inr,Set.mem_prod]

theorem pairedQuadratic_volume {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) :
    volume.real (ZSpan.fundamentalDomain (pairedQuadraticBasis hu hd hs ht))=
      5/(d^4*s^2*t^2) := by
  rw [pairedQuadraticDomain,Measure.real_def]
  change ((volume.prod volume) ((ZSpan.fundamentalDomain (quadraticScaledBasis hu hd hs ht)) ×ˢ
    (ZSpan.fundamentalDomain (quadraticScaledBasis hu hd hs ht)))).toReal = _
  rw [Measure.prod_prod,ENNReal.toReal_mul,← Measure.real_def,
    quadraticScaledBasis_volume hu hd hs ht]
  have hh : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  rw [← sq]
  field_simp
  nlinarith

end PairedQuadraticTiles

section PairedLatticeRiemann
open Classical Module MeasureTheory

noncomputable def pairedQuadraticEmbedding (d s t : ℝ) :
    (CutRing×CutRing) →ₗ[ℤ] ((Fin 2 → ℝ)×(Fin 2 → ℝ)) :=
  (quadraticScaledEmbedding d s t).prodMap (quadraticScaledEmbedding d s t)

theorem pairedQuadraticEmbedding_injective {d s t : ℝ} (hd : 0<d) (hs : 0<s) :
    Function.Injective (pairedQuadraticEmbedding d s t) := by
  intro z w hh
  exact Prod.ext (quadraticScaledEmbedding_injective hd hs (congrArg Prod.fst hh))
    (quadraticScaledEmbedding_injective hd hs (congrArg Prod.snd hh))

theorem pairedQuadratic_span {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) :
    Submodule.span ℤ (Set.range (pairedQuadraticBasis hu hd hs ht))=
      (pairedQuadraticEmbedding d s t).range := by
  rw [pairedQuadraticEmbedding,LinearMap.range_prodMap,← quadraticScaledBasis_span hu hd hs ht]
  ext x
  simp only [Submodule.mem_prod,Basis.mem_span_iff_repr_mem,pairedQuadraticBasis,
    Sum.forall,Basis.prod_repr_inl,Basis.prod_repr_inr]

noncomputable def pairedLatticeEquiv {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) :
    (CutRing×CutRing) ≃ₗ[ℤ] Submodule.span ℤ (Set.range (pairedQuadraticBasis hu hd hs ht)) :=
  (LinearEquiv.ofInjective (pairedQuadraticEmbedding d s t)
    (pairedQuadraticEmbedding_injective hd hs)).trans
    (LinearEquiv.ofEq _ _ (pairedQuadratic_span hu hd hs ht).symm)

@[simp] theorem pairedLatticeEquiv_coe {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) (z : CutRing×CutRing) :
    (pairedLatticeEquiv hu hd hs ht z : ((Fin 2 → ℝ)×(Fin 2 → ℝ)))=
      pairedQuadraticEmbedding d s t z := rfl

def pairedQuadraticBox (d s t R : ℝ) (q : (Fin 2 → ℝ)×(Fin 2 → ℝ)) : Set (CutRing×CutRing) :=
  {z | ‖q+pairedQuadraticEmbedding d s t z‖≤R}

theorem pairedQuadraticBox_rectangles {d s t R : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t)
    (q : (Fin 2 → ℝ)×(Fin 2 → ℝ)) (z : CutRing×CutRing) (hz : z∈pairedQuadraticBox d s t R q) :
    z.1∈cutRectangle ((-R-q.1 0)*(d*s)) ((-R-q.1 1)*(d*t)) (2*R*(d*s)) (2*R*(d*t)) ∧
    z.2∈cutRectangle ((-R-q.2 0)*(d*s)) ((-R-q.2 1)*(d*t)) (2*R*(d*s)) (2*R*(d*t)) := by
  have hnorm := norm_prod_le_iff.mp hz
  have hr : 0≤R := (norm_nonneg _).trans hz
  have hb (u : CutRing) (p : Fin 2 → ℝ) (hh : ‖p+quadraticScaledEmbedding d s t u‖≤R) :
      u∈cutRectangle ((-R-p 0)*(d*s)) ((-R-p 1)*(d*t)) (2*R*(d*s)) (2*R*(d*t)) := by
    have hj := (pi_norm_le_iff_of_nonneg hr).mp hh
    have h₀ := abs_le.mp (hj 0)
    have h₁ := abs_le.mp (hj 1)
    change -R≤p 0+ordinary u/(d*s) ∧ p 0+ordinary u/(d*s)≤R at h₀
    change -R≤p 1+conjugate u/(d*t) ∧ p 1+conjugate u/(d*t)≤R at h₁
    have ho : (-R-p 0)≤ordinary u/(d*s) ∧ ordinary u/(d*s)≤R-p 0 := by constructor <;> linarith
    have hc : (-R-p 1)≤conjugate u/(d*t) ∧ conjugate u/(d*t)≤R-p 1 := by constructor <;> linarith
    rw [le_div_iff₀ (mul_pos hd hs),div_le_iff₀ (mul_pos hd hs)] at ho
    rw [le_div_iff₀ (mul_pos hd ht),div_le_iff₀ (mul_pos hd ht)] at hc
    exact ⟨⟨ho.1,by nlinarith [ho.2]⟩,⟨hc.1,by nlinarith [hc.2]⟩⟩
  exact ⟨hb z.1 q.1 hnorm.1,hb z.2 q.2 hnorm.2⟩

theorem pairedQuadraticBox_finite {d s t R : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) (hR : 0<R)
    (q : (Fin 2 → ℝ)×(Fin 2 → ℝ)) : (pairedQuadraticBox d s t R q).Finite := by
  have h₁ := cutRectangle_finite ((-R-q.1 0)*(d*s)) ((-R-q.1 1)*(d*t))
    (2*R*(d*s)) (2*R*(d*t)) (by positivity)
  have h₂ := cutRectangle_finite ((-R-q.2 0)*(d*s)) ((-R-q.2 1)*(d*t))
    (2*R*(d*s)) (2*R*(d*t)) (by positivity)
  exact (h₁.prod h₂).subset (fun z hz => pairedQuadraticBox_rectangles hd hs ht q z hz)

theorem pairedQuadraticBox_card {d s t R : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) (hR : 0<R)
    (q : (Fin 2 → ℝ)×(Fin 2 → ℝ)) (S : Finset (CutRing×CutRing))
    (hS : ∀z∈S,z∈pairedQuadraticBox d s t R q) :
    (S.card:ℝ) ≤ (4*R^2*d^2*s*t+2)^2 := by
  let S₁ := S.image Prod.fst
  let S₂ := S.image Prod.snd
  have hsub : S⊆S₁×ˢS₂ := by
    intro z hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,
      Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
  have hc₁ : (S₁.card:ℝ)<4*R^2*d^2*s*t+2 := by
    have hh := cutRectangle_card_bound S₁ ((-R-q.1 0)*(d*s)) ((-R-q.1 1)*(d*t))
      (2*R*(d*s)) (2*R*(d*t)) (by positivity) (by positivity) (by
        intro u hu
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hu
        exact (pairedQuadraticBox_rectangles hd hs ht q z (hS z hz)).1)
    nlinarith
  have hc₂ : (S₂.card:ℝ)<4*R^2*d^2*s*t+2 := by
    have hh := cutRectangle_card_bound S₂ ((-R-q.2 0)*(d*s)) ((-R-q.2 1)*(d*t))
      (2*R*(d*s)) (2*R*(d*t)) (by positivity) (by positivity) (by
        intro u hu
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hu
        exact (pairedQuadraticBox_rectangles hd hs ht q z (hS z hz)).2)
    nlinarith
  have hcard : (S.card:ℝ)≤(S₁.card:ℝ)*(S₂.card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product S₁ S₂)
  exact hcard.trans (by nlinarith [Nat.cast_nonneg (α:=ℝ) S₁.card,Nat.cast_nonneg (α:=ℝ) S₂.card])

end PairedLatticeRiemann

end SimpleAmenable
end
end

end OAI
