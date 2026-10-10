import Mathlib
import OAI.Analysis.Conductivity.Branching.SmoothFamilyCorrectionTransport

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parametric_source_pullback
    (Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3))
    (hY : ∀ q x,(Y (q,x)).1=q)
    (hsm : ContDiff ℝ (↑(⊤:ℕ∞)) Y)
    (hinv : ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target)
    (p : P) {V : Set P} {O W K : Set Coord3}
    (hV : IsOpen V) (hp : p∈V) (hVb : Bornology.IsBounded V)
    (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hK : IsCompact K) (hKO : K⊆O) (hVO : V×ˢO⊆Y.target)
    (hW : ∀ q∈V,W⊆(fiberSlice Y hY q).symm '' K)
    {r : Fin 2 → P×Coord3 → ℝ} (hr : SmoothVanishingPairFamily p W r) :
    ∃ R : Fin 2 → P×Coord3 → ℝ,SmoothVanishingPairFamily p O R ∧
      ∀ᶠ q in 𝓝 p,(fun j x => R j (q,x))=(fun j => localPiolaSource (fiberSlice Y hY q) (fun x => r j (q,x))) := by
  obtain ⟨χ,hχ,hχc,hχs,_,hχone⟩ := exists_smooth_core_cutoff
    (isCompact_singleton.prod hK) (hV.prod hO) (hVb.prod hOb)
    (prod_mono (singleton_subset_iff.mpr hp) hKO)
  let w : P×Coord3 → ℝ := fun q => inverseSourceWeight (fiberSlice Y hY q.1).symm q.2
  have hw := parametric_inverseSourceWeight_smooth Y hY hsm hinv
  let g (j : Fin 2) : P×Coord3 → ℝ := fun q => w q*r j (q.1,(Y.symm q).2)
  have hg (j) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (g j) Y.target :=
    hw.mul ((hr.1 j).contDiffOn.comp (contDiff_fst.contDiffOn.prodMk
      (contDiff_snd.contDiffOn.comp hinv (fun _ _ => mem_univ _))) (fun _ _ => mem_univ _))
  let R : Fin 2 → P×Coord3 → ℝ := fun j q => χ q*g j q
  have hR (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (R j) :=
    smooth_mul_of_support_in_open Y.open_target (hg j) hχ (hχs.trans hVO)
  have hRq (q : P) (j) : tsupport (fun x => R j (q,x))⊆Prod.snd '' tsupport χ := by
    intro x hx
    have hc : (q,x)∈tsupport χ := (tsupport_comp_subset_preimage χ (continuous_const.prodMk continuous_id))
      (tsupport_mul_subset_left hx)
    exact ⟨(q,x),hc,rfl⟩
  refine ⟨R,⟨hR,fun j x => by simp only [R,g,hr.2.1 j _,mul_zero],
    Prod.snd '' tsupport χ,hχc.image continuous_snd,
    fun x hx => by rcases hx with ⟨z,hz,rfl⟩; exact (hχs hz).2,
    hRq⟩,?_⟩
  have hχnear : ∀ᶠ q in 𝓝 p,∀ x∈K,χ (q,x)=1 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    exact hχone (p,x) ⟨mem_singleton p,hx⟩
  filter_upwards [hV.mem_nhds hp,hχnear] with q hq hone
  funext j x
  let X := (fiberSlice Y hY q).symm
  have hXs : K⊆X.source := fun y hy => hVO ⟨hq,hKO hy⟩
  have hs : tsupport (fun x => r j (q,x))⊆X '' K := (hr.supported q j).trans (hW q hq)
  have hpr : tsupport (localPiolaSource X.symm (fun x => r j (q,x)))⊆K :=
    localPiolaSource_inverse_support X _ (hr.compact q j).2 hXs hs
  by_cases hx : (q,x)∈Y.target
  · have he : localPiolaSource (fiberSlice Y hY q) (fun y => r j (q,y)) x=g j (q,x) := by
      simp only [localPiolaSource,ite_eq_left (show x∈(fiberSlice Y hY q).target from hx)]
      rfl
    rw [he]
    by_cases hxK : x∈K
    · simp only [R,hone x hxK,one_mul]
    · have hz : g j (q,x)=0 := he.symm.trans (image_eq_zero_of_notMem_tsupport (fun h => hxK (hpr h)))
      simp only [R,hz,mul_zero]
  · have hc : χ (q,x)=0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hVO (hχs hh)))
    simp only [R,hc,zero_mul,localPiolaSource,ite_eq_right (show x∉(fiberSlice Y hY q).target from hx)]

end ScalarConductivity

end
end

end OAI
