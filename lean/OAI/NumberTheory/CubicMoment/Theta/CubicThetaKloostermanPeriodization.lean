import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramKernelCompact
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanFinite

namespace OAI

/-! Exact periodization of the off-diagonal row kernel over its finite
arithmetic residue classes. Absolute convergence comes from the actual
compact smooth inversion kernel. -/
noncomputable section
open scoped CompactlySupported ContDiff SchwartzMap
namespace CubicFirstMoment

def cubicThetaKloostermanRow (h k c : Eisenstein) (hc : (3:Eisenstein)∣c)
    (V : C_c(ℝ,ℂ)) (v : ℝ) (z : ℂ) : ℂ :=
  ∑' d : Eisenstein,cubicThetaKloostermanWeight h k c hc d*
    cubicThetaGramInversionKernel h k V (c:ℂ) (z+(d:ℂ)/(c:ℂ)) v

lemma cubicThetaKloostermanRow_summable (h k : Eisenstein) {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (V : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (V : ℝ → ℂ)) {δ v : ℝ} (hδ : 0<δ) (hv : 0<v)
    (hV : ∀ t≤δ,V t=0) (z : ℂ) :
    Summable (fun d : Eisenstein => cubicThetaKloostermanWeight h k c hc d*
      cubicThetaGramInversionKernel h k V (c:ℂ) (z+(d:ℂ)/(c:ℂ)) v) := by
  have hcC : (c:ℂ)≠0 := fun hz => hc0 (Subtype.ext hz)
  let F := cubicThetaGramKernelSchwartz h k V hsm hcC hδ hv hV
  have hf := schwartz_summable_eisenstein_coset F (c:ℂ)⁻¹ (inv_ne_zero hcC) z
  change Summable (fun d : Eisenstein =>
    cubicThetaGramInversionKernel h k V (c:ℂ) (z+(c:ℂ)⁻¹*(d:ℂ)) v) at hf
  have hf' : Summable (fun d : Eisenstein =>
      cubicThetaGramInversionKernel h k V (c:ℂ) (z+(d:ℂ)/(c:ℂ)) v) := by
    simpa only [div_eq_mul_inv,mul_comm] using hf
  apply Summable.of_norm_bounded hf'.norm
  intro d
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (cubicThetaKloostermanWeight_norm h k c hc d)
    (_root_.norm_nonneg _)).trans_eq (one_mul _)

theorem cubicThetaKloostermanRow_periodized (h k : Eisenstein) {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (V : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (V : ℝ → ℂ)) {δ v : ℝ} (hδ : 0<δ) (hv : 0<v)
    (hV : ∀ t≤δ,V t=0) (z : ℂ) :
    cubicThetaKloostermanRow h k c hc V v z=
      ∑' x : Residues (3*c),cubicThetaKloostermanWeight h k c hc (residueRepresentative (3*c) x)*
        ∑' m : Eisenstein,cubicThetaGramInversionKernel h k V (c:ℂ)
          (z+(residueRepresentative (3*c) x:ℂ)/(c:ℂ)+3*(m:ℂ)) v := by
  let e := Equiv.ofBijective (residueCosetMap (3*c))
    (residueCosetMap_bijective (mul_ne_zero (by norm_num) hc0))
  let G : Eisenstein → ℂ := fun d => cubicThetaKloostermanWeight h k c hc d*
    cubicThetaGramInversionKernel h k V (c:ℂ) (z+(d:ℂ)/(c:ℂ)) v
  have hG := cubicThetaKloostermanRow_summable h k hc hc0 V hsm hδ hv hV z
  have he (x : Residues (3*c)) (m : Eisenstein) : G (e (x,m))=
      cubicThetaKloostermanWeight h k c hc (residueRepresentative (3*c) x)*
        cubicThetaGramInversionKernel h k V (c:ℂ)
          (z+(residueRepresentative (3*c) x:ℂ)/(c:ℂ)+3*(m:ℂ)) v := by
    change cubicThetaKloostermanWeight h k c hc (residueRepresentative (3*c) x+(3*c)*m)*
      cubicThetaGramInversionKernel h k V (c:ℂ)
        (z+((residueRepresentative (3*c) x+(3*c)*m:Eisenstein):ℂ)/(c:ℂ)) v=_
    rw [cubicThetaKloostermanWeight_periodic h k hc hc0]
    congr 2
    push_cast
    rw [show ((3:Eisenstein):ℂ)=(3:ℂ) from rfl]
    have hcC : (c:ℂ)≠0 := fun hz => hc0 (Subtype.ext hz)
    field_simp
    ring
  unfold cubicThetaKloostermanRow
  change (∑' d,G d)=_
  rw [←e.tsum_eq]
  calc
    _ = ∑' x : Residues (3*c),∑' m : Eisenstein,G (e (x,m)) :=
      (e.summable_iff.mpr hG).tsum_prod
    _ = _ := by
      apply tsum_congr
      intro x
      simp_rw [he]
      exact tsum_mul_left

end CubicFirstMoment

end

end OAI
