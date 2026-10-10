import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.HilbertMainCases
import OAI.Probability.BinarySweep.FiniteLaws.HilbertTranspose
import OAI.Probability.BinarySweep.SparseBounds.FewSparse

namespace OAI

noncomputable section

section

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Sparse Young Irrep

theorem conditional_specht_many_sparse_eventually : ∀ᶠ s : ℕ in atTop,
    ∀ b r h k : ℕ, ∀ bits : Fin b → ℕ, gridSize bits=s → 16000≤b →
    (∀j, r≤bits j ∧ bits j≤2*r) → 4000000000≤(r:ℝ)*Real.log 2 →
    ((k+h:ℕ):ℝ)≤(s:ℝ)^(1599/1600:ℝ) → h≤100000*k →
    ∀ H : PathFamily bits h, ∀ μ : YoungDiagram, ∀ e : Cell μ ≃ FreeSlot H 0,
    ∀ _a : Tail μ ≃ Fin k, ∀z : ℝ, 0≤z → z≤linePerturbationRadius r →
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ)))≤Real.exp (-(k:ℝ)*Real.log s/16000) := by
  filter_upwards [many_collision_base_eventually] with s hs
  intro b r h k bits he hb hd hr hk hh H μ e a z hz hzr
  have hL : 4000000000*(b:ℝ)≤Real.log s := by
    have hl := grid_log_lower (fun j => (hd j).1)
    rw [he] at hl
    nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg b)]
  have hbase := hs b r h k bits he hb hd (by linarith) hk
  have hl0 : 0≤Real.log (s:ℝ) := (by positivity : (0:ℝ)≤4000000000*b).trans hL
  have hsmall := hbase.trans (show Real.exp (-Real.log s/4000)≤1 by
    rw [Real.exp_le_one_iff]; linarith)
  have hbound := conditional_specht_many_bound H μ e a (fun j => (hd j).2) hz hzr
    (hzr.trans_lt (linePerturbationRadius_lt_one r)) hsmall
  exact hbound.trans (many_hs_scalar b h k (by omega) (by exact_mod_cast hh) hL
    (by positivity) hbase)

end BinaryCoordinateSweeps

end

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open TraceHolder

lemma sum_pow_le_sum_pow {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀i,0≤a i)
    {q : ℕ} (hq : 0<q) : (∑i,a i^q) ≤ (∑i,a i)^q := by
  induction q, hq using Nat.le_induction with
  | base => simp
  | succ q hq ih =>
    have hs : 0≤∑i,a i := Finset.sum_nonneg (fun i _ => ha i)
    calc
      _ = ∑i,a i^q*a i := by simp only [pow_succ]
      _ ≤ ∑i,a i^q*(∑j,a j) := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i))
          (pow_nonneg (ha i) q))
      _ = (∑i,a i^q)*(∑j,a j) := by rw [Finset.sum_mul]
      _ ≤ (∑i,a i)^q*(∑j,a j) := mul_le_mul_of_nonneg_right ih hs
      _ = _ := (pow_succ _ _).symm

lemma evenMoment_le_one_pow {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {q : ℕ} (hq : 0<q) (A : V →ₗ[ℂ] V) :
    evenMoment q A ≤ (evenMoment 1 A)^q := by
  let v := stdOrthonormalBasis ℂ V
  rw [evenMoment_orthonormalMatrix v,evenMoment_orthonormalMatrix v]
  let M := LinearMap.toMatrixOrthonormal v A
  obtain ⟨U,W,s,hs,hU,hM,hg⟩ := exists_partial_svd M
  rw [matrixMoment_of_svd M q W s hg,matrixMoment_of_svd M 1 W s hg]
  simp only [mul_one]
  simp_rw [pow_mul]
  exact sum_pow_le_sum_pow (fun i => s i^2) (fun i => sq_nonneg _) hq

lemma evenMoment_le_exp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] {q : ℕ} (hq : 0<q) (A : V →ₗ[ℂ] V) (x : ℝ)
    (h : evenMoment 1 A≤Real.exp x) : evenMoment q A≤Real.exp ((q:ℝ)*x) := by
  calc
    _ ≤ (evenMoment 1 A)^q := evenMoment_le_one_pow hq A
    _ ≤ (Real.exp x)^q := pow_le_pow_left₀ (evenMoment_nonneg 1 A) h q
    _ = _ := (Real.exp_nat_mul x q).symm

end BinaryCoordinateSweeps.Irrep

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Sparse Young Irrep

def mainMomentPower : ℕ := 8000000000000

theorem sparse_uniform_radius : ∃ S : ℕ, ∀ r : ℕ, 2 ≤ r →
    4000000000 ≤ (r:ℝ)*Real.log 2 →
    ∃ δ : ℝ, 0<δ ∧ δ≤linePerturbationRadius r ∧ ∀ s : ℕ, S ≤ s →
    ∀ b h k : ℕ, ∀bits : Fin b → ℕ, gridSize bits=s → 1≤b →
    (∀j,r≤bits j ∧ bits j≤2*r) → (10:ℝ)^26≤Real.log s → 1≤k →
    ((k+h:ℕ):ℝ)≤(s:ℝ)^(1599/1600:ℝ) → h≤100000*k →
    ∀H : PathFamily bits h, ∀μ : YoungDiagram, ∀e : Cell μ ≃ FreeSlot H 0,
    ∀_a : Tail μ ≃ Fin k, ∀z : ℝ, 0≤z → z≤δ →
    (evenMoment mainMomentPower (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ))) ≤ Real.exp (-(4:ℝ)*k*Real.log s)) ∧
    (evenMoment mainMomentPower (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g*realSign g:ℂ))) ≤ Real.exp (-(4:ℝ)*k*Real.log s)) := by
  obtain ⟨S,hS⟩ := eventually_atTop.mp
    (conditional_specht_many_sparse_eventually.and many_collision_base_eventually)
  refine ⟨S,?_⟩
  intro r hr hrL
  obtain ⟨δ,hδ,hbound⟩ := sparse_finite_radius r hr
  refine ⟨min δ (linePerturbationRadius r),lt_min hδ (linePerturbationRadius_pos r),min_le_right _ _,?_⟩
  intro s hSs
  obtain ⟨hs,hc⟩ := hS s hSs
  intro b h k bits he hb hd hL hk htail hh H μ e a z hz hzr
  have hzδ := hzr.trans (min_le_left _ _)
  have hzline := hzr.trans (min_le_right _ _)
  have hone :
      (evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
        (fun g => (conditionalGroupLaw H z g:ℂ)))≤Real.exp (-(k:ℝ)*Real.log s/2000000000000)) ∧
      (evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
        (fun g => (conditionalGroupLaw H z g*realSign g:ℂ)))≤Real.exp (-(k:ℝ)*Real.log s/2000000000000)) := by
    by_cases hbB : b≤16000
    · have hhS : h≤gridSize bits := by
        have hec := Fintype.card_le_of_injective (H.position 0) (H.disjoint 0)
        simpa only [Fintype.card_fin,card_gridSlot] using hec
      have hkS : k≤gridSize bits := by
        have ht : ((k+h:ℕ):ℝ)≤gridSize bits := htail.trans
          (by rw [he]; exact Real.rpow_le_self_of_one_le (by exact_mod_cast (he ▸ gridSize_pos bits)) (by norm_num))
        have : k+h≤gridSize bits := by exact_mod_cast ht
        omega
      have hf := hbound b hb hbB bits hd h k hhS hkS (by simpa only [he] using hL) hk (by simpa only [he] using htail) hh H z hz hzδ
      constructor
      · exact (conditional_specht_hs H μ e a z).trans (by simpa only [he] using hf.1)
      · exact (conditional_signed_specht_hs H μ e a z).trans (by simpa only [he] using hf.2)
    · constructor
      · refine (hs b r h k bits he (by omega) hd hrL htail hh H μ e a z hz hzline).trans ?_
        apply Real.exp_le_exp.mpr
        have : 0≤(k:ℝ)*Real.log s := mul_nonneg (Nat.cast_nonneg _) (by linarith)
        linarith
      · let j : Fin b := ⟨0,by omega⟩
        have hbase := hc b r h k bits he (by omega) hd (by linarith) htail
        have hsmall : Real.exp (-Real.log s/4000)<1 := by rw [Real.exp_lt_one_iff]; linarith
        have hgeom := many_sparse_sign_geometry (hbase.trans_lt hsmall) j
        exact (conditional_signed_specht_many H μ e a z j (by have := (hd j).1; omega) hgeom).trans
          (Real.exp_pos _).le
  have hq : 0 < mainMomentPower := by norm_num [mainMomentPower]
  constructor
  · have h := evenMoment_le_exp hq _ _ hone.1
    convert h using 1
    congr 1
    norm_num [mainMomentPower]
    ring
  · have h := evenMoment_le_exp hq _ _ hone.2
    convert h using 1
    congr 1
    norm_num [mainMomentPower]
    ring

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Young Irrep

theorem sparse_closing_radius : ∃ S : ℕ, ∀r : ℕ, 2 ≤ r →
    4000000000 ≤ (r:ℝ)*Real.log 2 →
    ∃δ : ℝ, 0 < δ ∧ δ ≤ linePerturbationRadius r ∧ ∀s : ℕ, S ≤ s →
    ∀b h : ℕ, ∀bits : Fin b → ℕ, gridSize bits=s → 1 ≤ b →
    (∀j,r ≤ bits j ∧ bits j ≤ 2*r) → (10:ℝ)^26 ≤ Real.log s →
    ∀H : PathFamily bits h, ∀μ : YoungDiagram, ∀e : Cell μ ≃ FreeSlot H 0,
    diagramF μ < (s:ℝ)^(399/400:ℝ) → ∀z : ℝ, 0 ≤ z → z ≤ δ →
    evenMoment mainMomentPower (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ))) ≤
      Real.exp (-cExponent s*diagramF μ+eExponent s*h*Real.log s-pathCost H) := by
  obtain ⟨S,hS⟩ := sparse_uniform_radius
  obtain ⟨T,hT⟩ := eventually_atTop.mp sparse_reduction_eventually
  refine ⟨max S T,?_⟩
  intro r hr hrL
  obtain ⟨δ,hδ,hδline,hsp⟩ := hS r hr hrL
  refine ⟨δ,hδ,hδline,?_⟩
  intro s hSs
  have hs := hsp s ((le_max_left S T).trans hSs)
  have hred := hT s ((le_max_right S T).trans hSs)
  intro b h bits he hb hd hL H μ e hF z hz hzδ
  have := irreducible_comp_equiv e.symm.permCongrHom (hilbertSpecht μ)
  have hz1 := (hzδ.trans hδline).trans_lt (linePerturbationRadius_lt_one r)
  have hunit (g : Equiv.Perm (FreeSlot H 0)) (v : SpechtHilbert μ) :
      ‖((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom) g v‖=‖v‖ :=
    hilbertSpecht_unitary μ _ v
  by_cases ha : (1+cExponent s)*diagramF μ ≤ eExponent s*h*Real.log s-pathCost H
  · have hh := hilbert_conditional_automatic H z hz hz1 mainMomentPower _ hunit
    simp only [hilbertSpecht_finrank,he] at hh
    exact hh ha
  · obtain ⟨hk,hh,htail⟩ := hred b r h bits he hb (fun j => (hd j).1) (by linarith) H μ e hF ha
    let k := minTail μ
    have hm : Fintype.card (Cell μ) ≤ s := by
      rw [Fintype.card_congr e,card_freeSlot,he]
      exact Nat.sub_le _ _
    have hupper := diagramF_le_minTail μ s (he ▸ gridSize_pos bits) hm
    have hg := grid_parameter_allowance hb (fun j => (hd j).1) (by linarith : 400000000 ≤ (r:ℝ)*Real.log 2) H
    rw [he] at hg
    have hc : cExponent s ≤ 1 := by have := hg.1; unfold c0 at this; linarith
    have hallow : 0 ≤ eExponent s*h*Real.log s-pathCost H := by
      apply le_trans _ hg.2.2
      unfold e0
      positivity
    have hbound : evenMoment mainMomentPower
        (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
          (fun g => (conditionalGroupLaw H z g:ℂ))) ≤ Real.exp (-(4:ℝ)*k*Real.log s) := by
      rcases minTail_orientation μ with ht | ht
      · let a : Tail μ ≃ Fin k := (Fintype.equivFin _).trans (finCongr ht)
        exact (hs b h k bits he hb hd hL hk htail hh H μ e a z hz hzδ).1
      · let a : Tail μ.transpose ≃ Fin k := (Fintype.equivFin _).trans (finCongr ht)
        rw [conditional_transpose_moment]
        exact (hs b h k bits he hb hd hL hk htail hh H μ.transpose ((transposeCells μ).symm.trans e)
          a z hz hzδ).2
    refine hbound.trans (Real.exp_le_exp.mpr ?_)
    have hF0 := diagramF_nonneg μ
    change diagramF μ ≤ (k:ℝ)*Real.log s at hupper
    nlinarith [mul_le_mul_of_nonneg_right hc hF0]

end BinaryCoordinateSweeps

end

end OAI
