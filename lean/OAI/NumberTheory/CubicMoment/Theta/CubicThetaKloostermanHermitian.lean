import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteKloostermanIntertwiner

namespace OAI

/-! Pointwise Hermitian symmetry of the arithmetic Kloosterman matrix,
obtained from its proved finite self-adjoint operator. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaFiniteKloostermanApply_single (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (h k : Residues (3*c)) :
    cubicThetaFiniteKloostermanApply c hc0 (fun x => if x=k then 1 else 0) h=
      cubicThetaFiniteKloosterman c hc0 h k := by
  unfold cubicThetaFiniteKloostermanApply
  simp

lemma cubicThetaFiniteKloostermanIntertwiner_single (c : Eisenstein) (hc0 : c≠0)
    [Fintype (Residues (3*c))] (h k : Residues (3*c)) :
    cubicThetaFiniteKloostermanIntertwiner c hc0 (fun x => if x=k then 1 else 0) h=
      (Fintype.card (Residues (3*c)):ℂ)⁻¹*cubicThetaFiniteKloosterman c hc0 (-h) k := by
  rw [cubicThetaFiniteKloostermanIntertwiner_kernel,cubicThetaFiniteKloostermanApply_single]

theorem cubicThetaFiniteKloosterman_signed_hermitian {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (h k : Residues (3*c)) :
    cubicThetaFiniteKloosterman c hc0 (-h) k=
      star (cubicThetaFiniteKloosterman c hc0 (-k) h) := by
  let : Finite (Residues (3*c)) := finite_residues (mul_ne_zero (by norm_num) hc0)
  let : Fintype (Residues (3*c)) := Fintype.ofFinite _
  have he := cubicThetaFiniteKloostermanIntertwiner_symmetric hc hc0
    (fun x => if x=k then 1 else 0) (fun x => if x=h then 1 else 0)
  simp only [apply_ite,star_one,star_zero,mul_one,mul_zero,
    ite_mul,one_mul,zero_mul] at he
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] at he
  rw [cubicThetaFiniteKloostermanIntertwiner_single,
    cubicThetaFiniteKloostermanIntertwiner_single,star_mul,star_inv₀,star_natCast] at he
  have hn : (Fintype.card (Residues (3*c)):ℂ)≠0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Residues (3*c)))).ne'
  apply mul_left_cancel₀ (inv_ne_zero hn)
  exact he.trans (mul_comm _ _)

theorem cubicThetaFiniteKloosterman_hermitian {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (h k : Residues (3*c)) :
    cubicThetaFiniteKloosterman c hc0 h k=
      star (cubicThetaFiniteKloosterman c hc0 (-k) (-h)) := by
  simpa only [neg_neg] using cubicThetaFiniteKloosterman_signed_hermitian hc hc0 (-h) k

theorem cubicThetaKloostermanSum_hermitian {c : Eisenstein}
    (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (h k : Eisenstein) :
    cubicThetaKloostermanSum h k c hc=star (cubicThetaKloostermanSum (-k) (-h) c hc) := by
  rw [←cubicThetaFiniteKloosterman_integer h k hc hc0,
    ←cubicThetaFiniteKloosterman_integer (-k) (-h) hc hc0]
  simp only [map_neg]
  exact cubicThetaFiniteKloosterman_hermitian hc hc0 _ _

end CubicFirstMoment

end

end OAI
