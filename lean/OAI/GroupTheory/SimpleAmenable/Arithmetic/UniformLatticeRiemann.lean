import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.LatticeRiemann

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section UniformLatticeRiemann
open Classical Module MeasureTheory

theorem pairedQuadratic_riemann_uniform {d s t K : ℝ} (hd : 1≤d)
    (hs : 0<s) (ht : 0<t) (hst : 36≤ s*t) (hK : 0≤K)
    {f : ((Fin 2 → ℝ)×(Fin 2 → ℝ)) → ℝ} (hf : Integrable f)
    {A : NNReal} (hLip : LipschitzWith A f) (hzero : ∀x,K< ‖x‖ → f x=0)
    (q : (Fin 2 → ℝ)×(Fin 2 → ℝ)) :
    ∃S : Finset (CutRing×CutRing),
      (∀z,z∉S → f (q+pairedQuadraticEmbedding d s t z)=0) ∧
      |(5/(d^4*s^2*t^2))*(∑z∈S,f (q+pairedQuadraticEmbedding d s t z))-∫x,f x| ≤
        (5*(4*(K+1)^2+2)^2*(A:ℝ))*(6/(d*Real.sqrt (s*t))) := by
  let : (volume : Measure ((Fin 2 → ℝ)×(Fin 2 → ℝ))).IsAddLeftInvariant :=
    ⟨fun q => ((measurePreserving_add_left volume q.1).prod
      (measurePreserving_add_left volume q.2)).map_eq⟩
  have hd₀ : 0<d := lt_of_lt_of_le zero_lt_one hd
  let δ := 6/(d*Real.sqrt (s*t))
  have hroot : 6≤Real.sqrt (s*t) := by
    have hh := Real.sq_sqrt (mul_pos hs ht).le
    nlinarith [Real.sqrt_nonneg (s*t)]
  have hδ₀ : 0<δ := by dsimp [δ]; positivity
  have hδ₁ : δ≤1 := by
    apply (div_le_one (mul_pos hd₀ (Real.sqrt_pos.mpr (mul_pos hs ht)))).mpr
    nlinarith
  obtain ⟨u,hu,hcell⟩ := quadraticSmallTile hd₀ hs ht
  let b := pairedQuadraticBasis hu hd₀ hs ht
  let F := ZSpan.fundamentalDomain b
  let L := Submodule.span ℤ (Set.range b)
  let e := pairedLatticeEquiv hu hd₀ hs ht
  let S := (pairedQuadraticBox_finite hd₀ hs ht (show 0<K+δ by linarith) q).toFinset
  let : Countable CutRing := (QuadraticAlgebra.equivProd (1 : ℤ) 1).injective.countable
  let : Countable L.toAddSubgroup := e.symm.injective.countable
  let T : Finset L := S.image e
  have hF : IsAddFundamentalDomain L.toAddSubgroup F volume := ZSpan.isAddFundamentalDomain b volume
  have hFfinite : volume F<⊤ := (ZSpan.fundamentalDomain_isBounded b).measure_lt_top
  have hcell' : ∀x∈F,‖x‖≤δ := by
    intro x hx
    change x∈ZSpan.fundamentalDomain (pairedQuadraticBasis hu hd₀ hs ht) at hx
    rw [pairedQuadraticDomain] at hx
    exact norm_prod_le_iff.mpr ⟨hcell x.1 hx.1,hcell x.2 hx.2⟩
  have houtside (z : CutRing×CutRing) (hz : z∉S) : K+δ< ‖q+pairedQuadraticEmbedding d s t z‖ := by
    have hn : ¬z∈pairedQuadraticBox d s t (K+δ) q := by
      simpa only [S,Set.Finite.mem_toFinset] using hz
    exact lt_of_not_ge hn
  have hsupport : ∀z,z∉S → f (q+pairedQuadraticEmbedding d s t z)=0 := by
    intro z hz
    exact hzero _ (by linarith [houtside z hz])
  have hT : ∀z : L,z∉T → ∀x∈F,f (q+((z:((Fin 2 → ℝ)×(Fin 2 → ℝ)))+x))=0 := by
    intro z hz x hx
    have hz' : e.symm z∉S := by
      intro hh
      apply hz
      exact Finset.mem_image.mpr ⟨e.symm z,hh,e.apply_symm_apply z⟩
    have hbig := houtside (e.symm z) hz'
    have he : pairedQuadraticEmbedding d s t (e.symm z)=(z:((Fin 2 → ℝ)×(Fin 2 → ℝ))) := by
      change (e (e.symm z) : ((Fin 2 → ℝ)×(Fin 2 → ℝ)))=_
      rw [e.apply_symm_apply]
    rw [he] at hbig
    apply hzero
    have hnorm : ‖q+(z:((Fin 2 → ℝ)×(Fin 2 → ℝ)))‖ ≤
        ‖q+((z:((Fin 2 → ℝ)×(Fin 2 → ℝ)))+x)‖+‖x‖ := by
      have hh := norm_sub_le (q+((z:((Fin 2 → ℝ)×(Fin 2 → ℝ)))+x)) x
      simpa only [← add_assoc,add_sub_cancel_right] using hh
    have hh := hcell' x hx
    linarith
  have hft : Integrable (fun x => f (q+x)) :=
    (measurePreserving_add_left volume q).integrable_comp_of_integrable hf
  have hlipt : LipschitzWith A (fun x => f (q+x)) := by
    simpa only [mul_one,Function.comp_def] using hLip.comp (isometry_add_left q).lipschitzWith
  have herr := fundamentalDomain_riemann_error L.toAddSubgroup hF hFfinite hcell' hft hlipt T hT
  have hsum : (∑z∈T,f (q+(z:((Fin 2 → ℝ)×(Fin 2 → ℝ)))))=
      ∑z∈S,f (q+pairedQuadraticEmbedding d s t z) := by
    rw [Finset.sum_image (fun z _ w _ hh => e.injective hh)]
    rfl
  have hvol : volume.real F=5/(d^4*s^2*t^2) := pairedQuadratic_volume hu hd₀ hs ht
  change |volume.real F*(∑z∈T,f (q+(z:((Fin 2 → ℝ)×(Fin 2 → ℝ)))))-∫x,f (q+x)| ≤
    (T.card:ℝ)*((A:ℝ)*δ*volume.real F) at herr
  rw [hsum,integral_add_left_eq_self,hvol] at herr
  have hcard : T.card=S.card := Finset.card_image_of_injective _ e.injective
  rw [hcard] at herr
  have hSbox : ∀z∈S,z∈pairedQuadraticBox d s t (K+δ) q := by simp only [S,Set.Finite.mem_toFinset]; tauto
  have hcardbound := pairedQuadraticBox_card hd₀ hs ht (show 0<K+δ by linarith) q S hSbox
  have hH : 1≤d^2*s*t := by
    have hh : 1≤d^2 := by nlinarith
    have hst₁ : 1≤ s*t := by linarith
    nlinarith
  have hinside : 4*(K+δ)^2*d^2*s*t+2 ≤ (4*(K+1)^2+2)*(d^2*s*t) := by
    have he : (K+δ)^2≤(K+1)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right he (show 0≤d^2*s*t by positivity)
    nlinarith
  have hcard₁ : (S.card:ℝ) ≤ ((4*(K+1)^2+2)*(d^2*s*t))^2 :=
    hcardbound.trans (by gcongr)
  have hcv : (S.card:ℝ)*(5/(d^4*s^2*t^2)) ≤ 5*(4*(K+1)^2+2)^2 := by
    calc
      _ ≤ ((4*(K+1)^2+2)*(d^2*s*t))^2*(5/(d^4*s^2*t^2)) := by gcongr
      _ = _ := by field_simp
  refine ⟨S,hsupport,herr.trans ?_⟩
  calc
    _ = ((S.card:ℝ)*(5/(d^4*s^2*t^2)))*((A:ℝ)*δ) := by ring
    _ ≤ (5*(4*(K+1)^2+2)^2)*((A:ℝ)*δ) := mul_le_mul_of_nonneg_right hcv (by positivity)
    _ = _ := by ring

end UniformLatticeRiemann

end SimpleAmenable
end
end

end OAI
