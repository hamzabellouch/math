import Mathlib
import OAI.Analysis.Commutator.WeakOperatorAlgebra
import OAI.Analysis.Commutator.WeakOperatorLimit

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma inner_mono {A B : H →L[ℂ] H} (h : A≤B) (x : H) :
    (inner ℂ (A x) x).re≤(inner ℂ (B x) x).re := by
  have hp := ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr h)
  have hh : 0≤(inner ℂ ((B-A) x) x).re := hp.re_inner_nonneg_left x
  simpa only [sub_apply,inner_sub_left,Complex.sub_re,sub_nonneg] using hh

omit [CompleteSpace H] in
lemma nonneg_limit {l : Filter I} [l.NeBot] {T : I → H →L[ℂ] H} {W : H →L[ℂ] H}
    (ht : ∀ x y,Tendsto (fun i => inner ℂ (T i x) y) l (𝓝 (inner ℂ (W x) y)))
    (hp : ∀ᶠ i in l,0≤T i) : 0≤W := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  have hh : 0 ≤ inner ℂ (W x) x := ge_of_tendsto (ht x x) (hp.mono fun i hi =>
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hi).inner_nonneg_left x)
  exact ⟨Complex.ext (by simp) (by simpa using hh.2),hh.1⟩

omit [CompleteSpace H] in
lemma le_limit {l : Filter I} [l.NeBot] {T : I → H →L[ℂ] H} {W A : H →L[ℂ] H}
    (ht : ∀ x y,Tendsto (fun i => inner ℂ (T i x) y) l (𝓝 (inner ℂ (W x) y)))
    (hp : ∀ᶠ i in l,A≤T i) : A≤W := by
  apply sub_nonneg.mp
  refine nonneg_limit (T:=fun i => T i-A) ?_ (hp.mono fun _ hi => sub_nonneg.mpr hi)
  intro x y
  simpa only [sub_apply,inner_sub_left] using
    ((ht x y).sub (tendsto_const_nhds (x:=inner ℂ (A x) y)))

omit [CompleteSpace H] in
lemma limit_le {l : Filter I} [l.NeBot] {T : I → H →L[ℂ] H} {W A : H →L[ℂ] H}
    (ht : ∀ x y,Tendsto (fun i => inner ℂ (T i x) y) l (𝓝 (inner ℂ (W x) y)))
    (hp : ∀ᶠ i in l,T i≤A) : W≤A := by
  apply sub_nonneg.mp
  refine nonneg_limit (T:=fun i => A-T i) ?_ (hp.mono fun _ hi => sub_nonneg.mpr hi)
  intro x y
  simpa only [sub_apply,inner_sub_left] using
    ((tendsto_const_nhds (x:=inner ℂ (A x) y)).sub (ht x y))

lemma contraction_square_le {A : H →L[ℂ] H} (ha : 0≤A) (h1 : A≤1) : A*A≤A := by
  have hc : Commute A (1-A) := (Commute.one_right A).sub_right (Commute.refl A)
  have hh := hc.mul_nonneg ha (sub_nonneg.mpr h1)
  have he : A*(1-A)=A-A*A := by noncomm_ring
  rw [he] at hh
  exact sub_nonneg.mp hh

lemma contraction_norm_sq_le {A : H →L[ℂ] H} (ha : 0≤A) (h1 : A≤1) (x : H) :
    ‖A x‖^2≤(inner ℂ (A x) x).re := by
  have hh := inner_mono (contraction_square_le ha h1) x
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (IsSelfAdjoint.of_nonneg ha)
  have he : inner ℂ ((A*A) x) x=inner ℂ (A x) (A x) := hs (A x) x
  rw [he] at hh
  rw [norm_sq_eq_re_inner (𝕜:=ℂ)]
  exact hh

theorem exists_strong_inf (M : VonNeumannAlgebra H) (P : ℕ → H →L[ℂ] H)
    (hPM : ∀ n,P n∈M) (hpos : ∀ n,0≤P n) (hone : ∀ n,P n≤1) (hmono : Antitone P) :
    ∃ B : H →L[ℂ] H,B∈M ∧ 0≤B ∧ B≤1 ∧ (∀ n,B≤P n) ∧
      (∀ x,Tendsto (fun n => P n x) atTop (𝓝 (B x))) := by
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ)≤atTop := Ultrafilter.of_le atTop
  obtain ⟨B,hBn,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω P 1 zero_le_one
    (fun n => (CStarAlgebra.norm_le_one_iff_of_nonneg _ (hpos n)).mpr (hone n))
  have hBpos : 0≤B := nonneg_limit hlim (Eventually.of_forall hpos)
  have hB1 : B≤1 := limit_le hlim (Eventually.of_forall hone)
  have hBP (n : ℕ) : B≤P n := limit_le hlim
    (((eventually_ge_atTop n).filter_mono hω).mono fun m hnm => hmono hnm)
  refine ⟨B,WeakOperatorLimit.mem_vonNeumann hlim M (Eventually.of_forall hPM),hBpos,hB1,hBP,?_⟩
  intro x
  have hscalar : Tendsto (fun n => (inner ℂ ((P n-B) x) x).re) (ω : Filter ℕ) (𝓝 0) := by
    simpa only [sub_apply,inner_sub_left,Complex.sub_re,Function.comp_apply,sub_self]
      using (Complex.continuous_re.tendsto _ |>.comp (hlim x x)).sub (tendsto_const_nhds (x:=(inner ℂ (B x) x).re))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := (hscalar.eventually_lt_const (sq_pos_of_pos hε)).exists
  refine ⟨N,?_⟩
  intro n hn
  have hDpos : 0≤P n-B := sub_nonneg.mpr (hBP n)
  have hD1 : P n-B≤1 := (sub_le_self _ hBpos).trans (hone n)
  have hsq := contraction_norm_sq_le hDpos hD1 x
  have hle := inner_mono (sub_le_sub_right (hmono hn) B) x
  have hlt : ‖(P n-B) x‖<ε := by nlinarith [norm_nonneg ((P n-B) x)]
  simpa only [dist_eq_norm,sub_apply] using hlt

end Kadison.PositiveWOT

end

end
end

end OAI
