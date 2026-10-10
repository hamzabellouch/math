import Mathlib
import OAI.Geometry.PrescribedRicci.LocalDeterminantGain
import OAI.Geometry.PrescribedRicci.SchwartzHessianWords
import OAI.Geometry.PrescribedRicci.SobolevCommutatorBound
import OAI.Geometry.PrescribedRicci.UniformSchwartz

namespace OAI

/-! Uniform Local Gain. -/

section

 

noncomputable section
open Set Filter Topology Matrix _root_.MeasureTheory _root_.OAI.MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap Classical Matrix.Norms.Elementwise BoundedContinuousFunction
open scoped ComplexOrder MatrixOrder
namespace FrozenPoisson
open SobolevChart EllipticKernel MetricLocalization
variable {n : ℕ} {Z : Type*}
lemma uniform_schwartz_H2_of_differential {M : ℝ} (hM : 0 ≤ M)
    (H : Z → Matrix (Fin n) (Fin n) ℂ) (hH : ∀ z, (H z).PosDef)
    (hHM : ∀ z, ‖H z‖ ≤ M)
    (a : Z → BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (ha : ∀ z i j, (a z i j : EC n → ℂ).HasTemperateGrowth)
    (hsmall : ∀ z, perturbationBound (stdOrthonormalBasis ℝ (EC n)) (a z)*uniformEllipticBound n M ≤ 1/2)
    (F : Z → 𝓢(EC n,ℂ)) (hF : UniformSobolev 0 F)
    (hD : UniformSobolev 0 (fun z => schwartzDifferential (extendedCoefficient (H z) (a z)) (F z))) :
    UniformSobolev 2 F := by
  apply uniform_schwartz_H2 hM H hH hHM a ha hsmall F
    (fun z => F z-schwartzDifferential (extendedCoefficient (H z) (a z)) (F z)) (hF.sub hD)
  intro z
  rw [map_sub,schwartzDifferential_distribution _ (extendedCoefficient_temperate _ _ (ha z))]
end FrozenPoisson
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {Z : Type*}
lemma UniformSobolev.of_basis_words (k : ℕ) {s : ℝ} {F : Z → 𝓢(E,ℂ)}
    (h : ∀ ws : List (Fin (Module.finrank ℝ E)), ws.length ≤ k →
      UniformSobolev s (fun z => schwartzWord (ws.map (stdOrthonormalBasis ℝ E)) (F z))) :
    UniformSobolev (s+k) F := by
  induction k generalizing F with
  | zero => simpa [schwartzWord] using h [] (by simp)
  | succ k ih =>
    have hv := ih (fun ws hw => h ws (by omega))
    have hd (j : Fin (Module.finrank ℝ E)) := ih
      (F:=fun z => ∂_{stdOrthonormalBasis ℝ E j} (F z)) (fun ws hw => by
        have hh := h (ws++[j]) (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)
        simpa only [List.map_append,List.map_cons,List.map_nil,schwartzWord_append,schwartzWord,ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply,lineDerivOpCLM_apply] using hh)
    convert hv.raise_one hd using 1
    push_cast
    ring

lemma UniformSobolev.list_sum {ν : Type*} (L : List ν) {s : ℝ} (F : ν → Z → 𝓢(E,ℂ))
    (h : ∀ a ∈ L, UniformSobolev s (F a)) :
    UniformSobolev s (fun z => (L.map (fun a => F a z)).sum) := by
  induction L with
  | nil => simpa using UniformSobolev.const (Z:=Z) s (0 : 𝓢(E,ℂ))
  | cons a L ih =>
    simpa only [List.map_cons,List.sum_cons] using
      (h a (List.mem_cons_self)).add (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

lemma uniform_cutoff_commutator (κ : 𝓢(E,ℂ)) (ws : List E)
    {F : Z → 𝓢(E,ℂ)} (hF : UniformSobolev ((ws.length:ℝ)+1) F) :
    UniformSobolev 2 (fun z => schwartzWord ws (SchwartzMap.smulLeftCLM ℂ κ (F z))-
      SchwartzMap.smulLeftCLM ℂ κ (schwartzWord ws (F z))) := by
  simp_rw [schwartz_word_product_commutator,add_sub_cancel_left]
  apply UniformSobolev.list_sum
  intro p hp
  have hh := commutatorWords_orders ws p hp
  apply UniformSobolev.of_coreBound (hF.word (t:=2) p.2 (by
    have hlen : (p.2.length:ℝ)+1 ≤ ws.length := by exact_mod_cast (show p.2.length+1 ≤ ws.length by omega)
    linarith))
  exact coreBound_product_integer (schwartzWord p.1 κ) 2

lemma uniform_cutoff_word_gain (κ : 𝓢(E,ℂ)) (k : ℕ) {F : Z → 𝓢(E,ℂ)}
    (hF : UniformSobolev ((k:ℝ)+1) F)
    (h : ∀ ws : List (Fin (Module.finrank ℝ E)), ws.length ≤ k →
      UniformSobolev 2 (fun z => SchwartzMap.smulLeftCLM ℂ κ
        (schwartzWord (ws.map (stdOrthonormalBasis ℝ E)) (F z)))) :
    UniformSobolev ((k:ℝ)+2) (fun z => SchwartzMap.smulLeftCLM ℂ κ (F z)) := by
  have hh := UniformSobolev.of_basis_words (F:=fun z => SchwartzMap.smulLeftCLM ℂ κ (F z)) k (s:=2) (fun ws hw => by
    have hcom := uniform_cutoff_commutator κ (ws.map (stdOrthonormalBasis ℝ E))
      (hF.mono (by simp only [List.length_map]; exact_mod_cast (show ws.length+1 ≤ k+1 by omega)))
    convert (h ws hw).add hcom using 1
    funext z
    abel)
  simpa only [add_comm] using hh
end SobolevChart

end
end

end OAI
