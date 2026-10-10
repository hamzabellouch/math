import OAI.Analysis.StrictMeans.SmoothIndexHomotopy

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma quadratic_family_index {A B C : ℝ → ℝ}
    (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B) (hC : ContDiff ℝ 1 C)
    (hD : ∀ t∈Icc (0:ℝ) 1, A t*C t-(B t)^2≠0) {p : ℂ} {r : ℝ} (hr : 0<r) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ dist (meshPoint o s v) p ≤ r) →
      ∑ v∈S, heightIndex (fun w=>quadratic (A 0) (B 0) (C 0) (meshPoint o s w-p)) ex ey v =
      ∑ v∈S, heightIndex (fun w=>quadratic (A 1) (B 1) (C 1) (meshPoint o s w-p)) ex ey v := by
  have hu := quadraticFamily_contDiff hA hB hC p
  apply smooth_local_index_homotopy (quadraticFamily A B C p)
    (fun z=>hu.continuous.comp (continuous_id.prodMk continuous_const)) hr
  intro q hq
  apply quadraticFamily_regular hu.contDiffAt (hD _ hq.1)
  intro he
  have h := (mem_indexAnnulus.mp hq.2).1
  rw [he,dist_self] at h
  linarith

lemma quadratic_shear_x {a b c : ℝ} (ha : 0<a) (hD : a*c-b^2≠0)
    {p : ℂ} {r : ℝ} (hr : 0<r) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ dist (meshPoint o s v) p ≤ r) →
      ∑ v∈S, heightIndex (fun w=>quadratic a b c (meshPoint o s w-p)) ex ey v =
        if 0<a*c-b^2 then 1 else -1 := by
  let B : ℝ → ℝ := fun t=>(1-t)*b
  let C : ℝ → ℝ := fun t=>(a*c-b^2+(B t)^2)/a
  have hB : ContDiff ℝ 1 B := (contDiff_const.sub contDiff_id).mul contDiff_const
  have hC : ContDiff ℝ 1 C := (contDiff_const.add (hB.pow 2)).div_const a
  have hdet (t : ℝ) : a*C t-(B t)^2=a*c-b^2 := by dsimp [C]; field_simp; ring
  have hh := quadratic_family_index (A:=fun _=>a) contDiff_const hB hC
    (fun t _=>by rw [hdet]; exact hD) (p:=p) hr
  have hC0 : C 0=c := by dsimp [C,B]; field_simp; ring
  have hC1 : C 1=(a*c-b^2)/a := by simp [C,B]
  have hd : (a*c-b^2)/a≠0 := div_ne_zero hD ha.ne'
  filter_upwards [hh,gt_mem_nhds hr] with s hs hsbound
  intro hspos o S hS
  have he := hs hspos o S hS
  simp only [B,sub_zero,one_mul,sub_self,zero_mul,hC0,hC1] at he
  rw [he,diagonal_local_sum ha.ne' hd hspos hsbound.le hS]
  have hsign : 0<(a*c-b^2)/a ↔ 0<a*c-b^2 := div_pos_iff_of_pos_right ha
  simp only [ha,ite_true,one_mul,hsign]

lemma quadratic_shear_y {a b c : ℝ} (hc : 0<c) (hD : a*c-b^2≠0)
    {p : ℂ} {r : ℝ} (hr : 0<r) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ dist (meshPoint o s v) p ≤ r) →
      ∑ v∈S, heightIndex (fun w=>quadratic a b c (meshPoint o s w-p)) ex ey v =
        if 0<a*c-b^2 then 1 else -1 := by
  let B : ℝ → ℝ := fun t=>(1-t)*b
  let A : ℝ → ℝ := fun t=>(a*c-b^2+(B t)^2)/c
  have hB : ContDiff ℝ 1 B := (contDiff_const.sub contDiff_id).mul contDiff_const
  have hA : ContDiff ℝ 1 A := (contDiff_const.add (hB.pow 2)).div_const c
  have hdet (t : ℝ) : A t*c-(B t)^2=a*c-b^2 := by dsimp [A]; field_simp; ring
  have hh := quadratic_family_index hA hB (C:=fun _=>c) contDiff_const
    (fun t _=>by rw [hdet]; exact hD) (p:=p) hr
  have hA0 : A 0=a := by dsimp [A,B]; field_simp; ring
  have hA1 : A 1=(a*c-b^2)/c := by simp [A,B]
  have hd : (a*c-b^2)/c≠0 := div_ne_zero hD hc.ne'
  filter_upwards [hh,gt_mem_nhds hr] with s hs hsbound
  intro hspos o S hS
  have he := hs hspos o S hS
  simp only [B,sub_zero,one_mul,sub_self,zero_mul,hA0,hA1] at he
  rw [he,diagonal_local_sum hd hc.ne' hspos hsbound.le hS]
  have hsign : 0<(a*c-b^2)/c ↔ 0<a*c-b^2 := div_pos_iff_of_pos_right hc
  simp only [hc,ite_true,mul_one,hsign]

lemma quadratic_local_index {a b c : ℝ} (htr : 0<a+c) (hD : a*c-b^2≠0)
    {p : ℂ} {r : ℝ} (hr : 0<r) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ dist (meshPoint o s v) p ≤ r) →
      ∑ v∈S, heightIndex (fun w=>quadratic a b c (meshPoint o s w-p)) ex ey v =
        if 0<a*c-b^2 then 1 else -1 := by
  by_cases ha : 0<a
  · exact quadratic_shear_x ha hD hr
  · exact quadratic_shear_y (by linarith) hD hr

end
end StrictInverseFirstPower.Grid

end

end OAI
