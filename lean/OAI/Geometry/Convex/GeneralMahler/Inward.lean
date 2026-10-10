import OAI.Geometry.Convex.GeneralMahler.AngleIntegral

namespace OAI
/-! A Brouwer inward estimate using spectral boxes directly for the transform B
instead of round Frobenius balls in Q=log B. In particular the extreme
eigenvectors alone suffice. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
open Layers ProjField
variable {m : ℕ} [NeZero m]

lemma poly_cut (m:ℕ) (K:ℝ) : PolyBound fun x:ℝ=> cutoffC m (K*x^2) := by
  let f := fun x:ℝ=>K*x^2
  have hf : PolyBound f := (PolyBound.const _).mul (PolyBound.id.pow _)
  have he : PolyBound (fun x:ℝ=> f x * (m:ℝ) * f x ^ 2 * (a 0)⁻¹) :=
    (((hf.mul (PolyBound.const _)).mul (hf.pow _)).mul (PolyBound.const _))
  simp only [cutoffC,div_eq_mul_inv]
  exact (PolyBound.const _).add (((PolyBound.const _).mul hf).mul (hf.add he))

lemma inv_lim (D L : ℝ) :
    ∀ᶠ N : ℝ in atTop, D*(N/N^2*L+ek N) ≤ 1/2 := by
  have h : Tendsto (fun N:ℝ=>D*(N⁻¹*L+ek N)) atTop (𝓝 0) := by
    have he := ((tendsto_inv_atTop_zero (𝕜:=ℝ)).mul_const L).add ekrapid.tail_limit
    simpa using he.const_mul D
  filter_upwards [h.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)), eventually_gt_atTop (0:ℝ)]
    with N hn hp
  change D*(N⁻¹*L+ek N)<_ at hn
  rw [show N/N^2=N⁻¹ from by field_simp]
  exact hn.le

lemma area_lim (D A K : ℝ) (m:ℕ) :
    ∀ᶠ N : ℝ in atTop,
      let C := cutoffC m (K*N^2)
      D*N/N^2*8 + D*ek N*(C*(1+N)) + A*ek N*C ≤ 1/2 := by
  let C := fun N:ℝ => cutoffC m (K*N^2)
  have h₁ := (ekrapid.product (poly_cut m K)).tail_limit
  have h₂ := (ekrapid.product ((poly_cut m K).mul
    ((PolyBound.const (1:ℝ)).add PolyBound.id))).tail_limit
  let f := fun N:ℝ=> D*N⁻¹*8 + D*(ek N*(C N*(1+N))) + A*(ek N*C N)
  have he : Tendsto f atTop (𝓝 0) := by
    have hh := ((((tendsto_inv_atTop_zero (𝕜:=ℝ)).const_mul D).mul_const 8).add
      (h₂.const_mul D)).add (h₁.const_mul A)
    simpa [C,f] using hh
  filter_upwards [he.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)), eventually_gt_atTop (0:ℝ)]
    with N hn hp
  change f N < 1/2 at hn
  intro c
  rw [show D*N/N^2=D*N⁻¹ from by field_simp,mul_assoc D (ek N),mul_assoc A (ek N)]
  exact hn.le

theorem inward (q₀:ProjField m) :
    ∃ R≥(2:ℝ), ∀ hr:0<R, ∀ x:Param m R, ∀ v:Rn m, ‖v‖=1 →
      let A := (x.instanceQ hr q₀).avgA
      (op x.B v= R⁻¹ • v → 0 ≤ ⟪v,op A v⟫) ∧
      (op x.B v= R • v → ⟪v,op A v⟫ ≤ 0) := by
  obtain ⟨K,hK⟩ := q₀.Field_isBound
  obtain ⟨D,hD,h₁⟩ := angle_est q₀
  obtain ⟨B,hB,h₂⟩ := dir_tail_area m
  obtain ⟨W,hW,h₃⟩ := small_minus_bound m hD
  let L := 2*W
  have h : ∀ᶠ N:ℝ in atTop,
      4 ≤ N ∧ D*(N/N^2*(4/a (-1))+ek N) ≤ 1/2 ∧
      D*(N/N^2*a L+ek N) ≤ 1/2 ∧
      (let C := cutoffC m (K*N^2)
       D*N/N^2*8 + D*ek N*(C*(1+N))+B*ek N*C ≤ 1/2) :=
    (eventually_ge_atTop _).and ((inv_lim D _).and ((inv_lim D _).and (area_lim D B K m)))
  obtain ⟨N,hN,ha,hb,hc⟩ := h.exists
  let R := N^2
  have hr₀ : 2≤R := by dsimp [R]; nlinarith
  have hn : 1≤N := by linarith
  use R, hr₀
  intro hr x v hv A
  let q := x.instanceQ hr q₀
  have hh := h₁ R hr x v hv
  have hw : ⟪v,op A v⟫=q.plus v-q.minus v := q.pn _ hv
  rw [hw]
  constructor
  · intro he
    have hq := h₃ q v hv R hr₀ (fun z j hj=>(hh z j hj).1 he)
    have ht : 0≤L := mul_nonneg (by norm_num) hW
    have hp := small_plus_lower q v hv hD hr hn ht (fun z=>(hh z N hn).1 he) hb
    unfold L at hp
    linarith
  intro he
  have hy := large_minus_lower hr x q₀ v hv hD hn ha (fun z=>(hh z N hn).2 he)
  let C := cutoffC m (K*N^2)
  have ht := x.Bound_instance hr₀ hr hK
  let l := C*(1+N)
  have he' : 1≤C := (positive_exact m ht.one_le).1
  have hl : 0 ≤ l := by unfold l; nlinarith
  have hz := large_core_upper hr x q₀ v hv hD hn hl (fun z=>(hh z N hn).2 he)
  have hf : q.plus v ≤ 1/2 := calc
    _ = _ := plus_split _ _ hv hl
    _ ≤ _ := add_le_add hz (h₂ _ q ht v hv N hN)
    _ ≤ _ := hc
  change 1/2 ≤ q.minus v at hy
  linarith
end GeneralMahler

end

end OAI
