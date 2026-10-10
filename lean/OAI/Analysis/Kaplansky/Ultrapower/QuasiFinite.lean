import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.QuasiNull

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] (V : QuasiValue A)

lemma finite_mod_null (x : A)
    (hx : IsNull V (star x*x-1)) : IsNull V (x*star x-1) := by
  let : Nontrivial A := nontrivial_of_ne (1:A) 0 (fun h =>
    zero_ne_one (V.zero.symm.trans ((congrArg V.val h.symm).trans V.one)))
  let I := nullIdeal V
  let q := I.mkStarAlgHom
  have hsmul (r : ℝ) (a : A) : q (r • a) = r • q a :=
    q.toAlgHom.map_smul_of_tower r a
  have qzero (a : A) : q a = 0 ↔ IsNull V a := I.mk_eq_zero a
  have hiso : star (q x)*q x = 1 := by
    have h := (qzero _).2 hx
    simpa only [map_sub,map_mul,map_star,map_one,sub_eq_zero] using h
  have hp : IsStarProjection (q x*star (q x)) := by
    refine ⟨?_, (mul_star_self_nonneg _).isSelfAdjoint⟩
    change (q x*star (q x))*(q x*star (q x))=q x*star (q x)
    calc _ = q x*(star (q x)*q x)*star (q x) := by noncomm_ring
         _ = _ := by rw [hiso,mul_one]
  let w := 1-q x*star (q x)
  have hw : 0 ≤ w := hp.one_sub.nonneg
  obtain ⟨y, hy⟩ := I.mk_surjective (CFC.sqrt w)
  change q y = CFC.sqrt w at hy
  let u := star y*y
  have hu : 0 ≤ u := star_mul_self_nonneg y
  have hqu : q u = w := by
    simp only [u,map_mul,map_star,hy,(CFC.sqrt_nonneg w).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self w hw
  let c := ‖x*star x‖+1
  have hc : 0 ≤ c-1 := by dsimp [c]; linarith [norm_nonneg (x*star x)]
  have ha : 0 ≤ c • (1 : A)-x*star x := by
    apply sub_nonneg.mpr
    have ht := (mul_star_self_nonneg x).isSelfAdjoint.le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at ht
    exact ht.trans (smul_le_smul_of_nonneg_right (by dsimp [c]; linarith) zero_le_one)
  have hb : 0 ≤ u + (c-1) • (1 : A) := add_nonneg hu (smul_nonneg hc zero_le_one)
  have hab : IsNull V ((c • (1 : A)-x*star x) - (u+(c-1) • 1)) := by
    apply (qzero _).1
    simp only [map_sub,map_add,map_mul,map_star,map_one,hsmul,hqu]
    dsimp [w]
    rw [sub_smul,one_smul]
    abel
  have hvx : V.val (x*star x) = 1 := by
    rw [V.square_swap]
    exact (val_eq_of_null_sub V (star_mul_self_nonneg x) zero_le_one hx).trans V.one
  have hv := val_eq_of_null_sub V ha hb hab
  rw [V.val_scalar_sub (mul_star_self_nonneg x).isSelfAdjoint,
    V.val_shift hu.isSelfAdjoint (c-1),hvx] at hv
  have hvu : V.val u = 0 := by linarith
  have hnull := null_of_val_zero V hu hvu
  have hqu0 := (qzero _).2 hnull
  have hw0 : w=0 := hqu.symm.trans hqu0
  apply (qzero _).1
  simp only [map_sub,map_mul,map_star,map_one]
  exact sub_eq_zero.mpr (sub_eq_zero.mp hw0).symm

abbrev FaithfulQuotient := V.nullIdeal.Quotient
abbrev quotientHom : A →⋆ₐ[ℂ] V.FaithfulQuotient := V.nullIdeal.mkStarAlgHom

lemma faithfulQuotient_nontrivial : Nontrivial V.FaithfulQuotient := by
  apply nontrivial_of_ne (1:V.FaithfulQuotient) 0
  intro h
  have h' : V.IsNull 1 := (V.nullIdeal.mk_eq_zero 1).mp ((map_one V.quotientHom).trans h)
  have hv : V.val 1=0 := by simpa only [IsNull,star_one,one_mul] using h'
  exact zero_ne_one (hv.symm.trans V.one)

lemma faithfulQuotient_finite (x : V.FaithfulQuotient) (hx : star x*x=1) : x*star x=1 := by
  obtain ⟨a,ha⟩ := V.nullIdeal.mk_surjective x
  change V.quotientHom a=x at ha
  subst x
  have hn : V.IsNull (star a*a-1) := by
    apply (V.nullIdeal.mk_eq_zero _).mp
    change V.quotientHom (star a*a-1)=0
    simpa only [map_sub,map_mul,map_star,map_one,sub_eq_zero] using hx
  have hh := (V.nullIdeal.mk_eq_zero _).mpr (V.finite_mod_null a hn)
  change V.quotientHom (a*star a-1)=0 at hh
  simpa only [map_sub,map_mul,map_star,map_one,sub_eq_zero] using hh


end KaplanskyConsequences.QuasiValue

end

end OAI
