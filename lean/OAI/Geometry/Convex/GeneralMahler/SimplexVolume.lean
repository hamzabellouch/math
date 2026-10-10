import OAI.Geometry.Convex.GeneralMahler.SimplexCone
import OAI.Geometry.Convex.GeneralMahler.Santalo

namespace OAI
/-! Simplex direction of equality, solved by sending the cone to an orthant. -/
noncomputable section
open Filter Set MeasureTheory Real Module
open scoped RealInnerProductSpace ENNReal
namespace GeneralMahler
namespace Body
variable {n : ℕ}

theorem simplex_attains {K : Body n} (hK : IsSimplex (K:Set (Rn n))) :
    K.P = ((n:ℝ)+1)^(n+1)/(n.factorial:ℝ)^2 := by
  obtain ⟨b,hbt,hb⟩ := exists_basis_of_simplex hK
  let m : ℝ := (n:ℝ)+1
  have hm : 0 < m := by dsimp [m]; positivity
  let a : OrthonormalBasis (Fin (n+1)) ℝ (LiftSpace n) :=
    (stdOrthonormalBasis ℝ _).reindex (finCongr (lift_finrank n))
  let B := rebase b a.toBasis
  let V := pair 1 (0:Rn n)
  let D := orthant a.toBasis
  let ef := a.toBasis.equivFun
  let c := fun x => ef (B x)
  have hcoord (x : LiftSpace n) : c x = b.equivFun x :=
    a.toBasis.equivFun.apply_symm_apply _
  have he : pushCone B K.cone = D := by
    rw [hb]
    exact pushCone_rebase b _
  have hv : ∀ i, ef (contra B V) i = 1 := by
    intro i
    dsimp only [ef]
    rw [eq_basis_ip]
    have ha : (a i) = B (b i) := by
      simpa only [OrthonormalBasis.coe_toBasis] using (rebase_apply_basis b a.toBasis i).symm
    rw [ha, pair_contra]
    rw [← hgt_horiz_pair (b i)]
    change ⟪pair _ _, pair _ _⟫ = _
    rw [pair_inner,inner_zero_right,add_zero,hbt,one_mul]
  have hiv : contra B V ∈ interior (D : Set (LiftSpace n)) :=
    (mem_interior_orthant a.toBasis).mpr fun i => by rw [hv]; norm_num
  let M := fun z : Rn n => pair m (m • z)
  have hsum (x : LiftSpace n) : ∑ i, c x i = hgt x := by
    have H := congrArg hgtL (sum_coords b x)
    simp only [_root_.map_sum,map_smul, hgtL_apply, smul_eq_mul,hbt, mul_one] at H
    rw [hcoord]; exact H
  let k : ℝ := (m^ (n+1)) / (n.factorial:ℝ)^2
  have hk : 0 < k := by dsimp [k]; positivity
  have hn (z : Rn n) (hz : z ∈ interior (K:Set (Rn n))) :
      (∀ i, 0 < c (M z) i) ∧ K.productAt z = k * ∏ i, (c (M z) i)⁻¹ := by
    have hh : B (M z) ∈ interior (D : Set (LiftSpace n)) := by
      rw [← he,apply_mem_interior_pushCone]
      exact (K.pair_mem_interior_cone_iff m hm _).mpr hz
    refine ⟨(mem_interior_orthant a.toBasis).mp hh,?_⟩
    have He := chi_transform B K.cone (M z) V
    rw [he, orthant_self_dual a, chi_orthant a hiv, chi_orthant a hh] at He
    change (∏ i, (ef _ i)⁻¹) * (∏ i, (ef _ i)⁻¹) = _ at He
    simp_rw [hv] at He
    have H : (m⁻¹)^(n+1)*(n.factorial:ℝ)^2*K.productAt z = ∏ i, (c (M z) i)⁻¹ := by
      change _*_*((volume _).toReal*(volume _).toReal) = _
      rw [← cone_volume K z hz m hm]
      change chi K.cone V * chi (posDual K.cone) (M z) = _
      rw [← He]
      simp only [inv_one, Finset.prod_const_one, one_mul]; rfl
    rw [← H]; dsimp only [k]
    rw [inv_pow]
    field_simp
  obtain ⟨z,hz,heq⟩ :
      ∃ z ∈ interior (K:Set (Rn n)), K.productAt z = k := by
    let p := b.equivFun.symm (fun _ => 1)
    have hp : c p = fun _ => 1 := (hcoord p).trans (b.equivFun.apply_symm_apply _)
    have hgtp := (hsum p).symm
    rw [hp] at hgtp
    have hg : hgt p = m := by simpa [m] using hgtp
    have hin : p ∈ interior (K.cone : Set (LiftSpace n)) := by
      rw [hb,mem_interior_orthant, ← hcoord,hp]
      intro i; norm_num
    let x := m⁻¹ • horiz p
    have he : M x = p := by
      dsimp only [M,x]
      rw [smul_smul,mul_inv_cancel₀ hm.ne',one_smul, ← hg,hgt_horiz_pair]
    have hx : x ∈ interior (K:Set (Rn n)) :=
      (K.pair_mem_interior_cone_iff m hm x).mp ((he.symm ▸ hin) : M x ∈ _)
    exact ⟨x,hx,by rw [(hn x hx).2,he,hp]; simp⟩
  change K.P = k
  apply le_antisymm ((product_min hz).trans_eq heq)
  let w := K.santalo
  change k ≤ K.productAt w
  obtain ⟨hw',hh⟩ := hn w K.santalo_spec.1
  set d := c (M w) with hdef
  have hd (i) : 0 < d i := hw' i
  have hl : ∑ i, Real.log (d i) ≤ 0 := calc
    _ ≤ ∑ i, (d i - 1) := Finset.sum_le_sum (fun i _ => log_le_sub_one_of_pos (hd i))
    _ = 0 := by rw [Finset.sum_sub_distrib,hdef,hsum]; simp [M,m]
  have h₂ : 1 ≤ ∏ i, (d i)⁻¹ := calc
    1 ≤ Real.exp (-∑ i, Real.log (d i)) := by
      have h := Real.exp_le_exp.mpr (show 0 ≤ -∑ i, Real.log (d i) from neg_nonneg.mpr hl)
      rwa [Real.exp_zero] at h
    _ = ∏ i, (d i)⁻¹ := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      exact Finset.prod_congr rfl fun i _ => by rw [Real.exp_neg, Real.exp_log (hd i)]
  rw [hh]
  exact le_mul_of_one_le_right hk.le h₂

end Body
end GeneralMahler

end

end OAI
