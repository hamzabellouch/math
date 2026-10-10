import OAI.Analysis.AncientFlat.Evolution.FiniteCoreApply
import OAI.Analysis.AncientFlat.Regularity.CoreCorrectionHolder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace CompactCoreFinite
open CompactCore
open ParabolicInterior ParabolicLowerOrder
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma correction_jet_holder {α M : ℝ} {Ω : Set (V × ℝ)} (hα : 0<α) (hα1 : α<1)
    (hx : ∀ p∈Ω, ‖p.1‖≤1) (f : ℝ → V → ℂ) (hM : 0≤M)
    (hf : ∀ p∈Ω, ContDiff ℝ 4 (f p.2))
    (hb : ∀ j : ℕ, j≤4 → HolderBound α Ω (fun p => iteratedFDeriv ℝ j (f p.2) p.1) M) :
    ∀ j : ℕ, j≤2 → HolderBound α Ω
      (fun p => iteratedFDeriv ℝ j (correction (f p.2)) p.1) (720*M) := by
  have hd (p : V × ℝ) (hp : p∈Ω) : ContDiff ℝ 3 (fderiv ℝ (f p.2)) := (hf p hp).fderiv_right (by norm_num)
  have hdd (p : V × ℝ) (hp : p∈Ω) : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ (f p.2))) := (hd p hp).fderiv_right (by norm_num)
  have hb1 : ∀ j : ℕ, j≤2 → HolderBound α Ω
      (fun p => iteratedFDeriv ℝ j (fderiv ℝ (f p.2)) p.1) M := by
    intro j hj
    exact fderiv_jet_holder f j (hb (j+1) (by omega))
  have hb2 : ∀ j : ℕ, j≤2 → HolderBound α Ω
      (fun p => iteratedFDeriv ℝ j (fderiv ℝ (fderiv ℝ (f p.2))) p.1) M := by
    intro j hj
    exact fderiv_jet_holder (fun t => fderiv ℝ (f t)) j
      (fderiv_jet_holder f (j+1) (hb (j+1+1) (by omega)))
  have hi := id_jet_holder hα hα1 hx
  have h1 := apply_jet_holder (fun t => fderiv ℝ (f t)) (fun _ => id) (fun p hp => (hd p hp).of_le (by norm_num)) (fun _ _ => contDiff_id)
    hM (by norm_num : (0:ℝ)≤2) hb1 hi
  have h2 := apply_jet_holder (fun t => fderiv ℝ (fderiv ℝ (f t))) (fun _ => id) hdd
    (fun _ _ => contDiff_id) hM (by norm_num : (0:ℝ)≤2) hb2 hi
  have h3 := apply_jet_holder (fun t y => fderiv ℝ (fderiv ℝ (f t)) y y) (fun _ => id)
    (fun p hp => (hdd p hp).clm_apply contDiff_id) (fun _ _ => contDiff_id)
    (by positivity : 0≤8*M*2) (by norm_num : (0:ℝ)≤2) h2 hi
  intro j hj
  have ht := (h3 j hj).add ((h1 j hj).const_smul 29)
  have he (p : V × ℝ) (hp : p∈Ω) : iteratedFDeriv ℝ j (correction (f p.2)) p.1= iteratedFDeriv ℝ j (fun y => fderiv ℝ (fderiv ℝ (f p.2)) y y y) p.1+
        (29:ℝ) • iteratedFDeriv ℝ j (fun y => fderiv ℝ (f p.2) y y) p.1 := by
    have ha : ContDiff ℝ (j:ℕ∞ω) (fun y => fderiv ℝ (fderiv ℝ (f p.2)) y y y) := by
      simpa only [id_eq] using (((hdd p hp).clm_apply contDiff_id).clm_apply contDiff_id).of_le
        (by exact_mod_cast hj)
    have hb' : ContDiff ℝ (j:ℕ∞ω) (fun y => fderiv ℝ (f p.2) y y) := by
      simpa only [id_eq] using ((hd p hp).clm_apply contDiff_id).of_le
        (by exact_mod_cast (show j≤3 by omega))
    have hs : correction (f p.2)=(fun y => fderiv ℝ (fderiv ℝ (f p.2)) y y y)+
        (fun y => (29:ℝ) • fderiv ℝ (f p.2) y y) := by
      funext y
      simp only [correction,radialJet,iteratedFDeriv_two_apply,iteratedFDeriv_one_apply,
        Pi.add_apply,Complex.real_smul]
      norm_num
    rw [hs,iteratedFDeriv_add ha (hb'.const_smul (29:ℝ)),Pi.add_apply,
      iteratedFDeriv_const_smul_apply' hb'.contDiffAt]
  have hc : 8*(8*M*2)*2+|(29:ℝ)| *(8*M*2)=720*M := by norm_num; ring
  rw [hc] at ht
  constructor
  · intro p hp
    change ‖iteratedFDeriv ℝ j (correction (f p.2)) p.1‖≤_
    rw [he p hp]
    exact ht.1 p hp
  · intro p hp q hq
    change ‖iteratedFDeriv ℝ j (correction (f p.2)) p.1-iteratedFDeriv ℝ j (correction (f q.2)) q.1‖≤_
    rw [he p hp,he q hq]
    exact ht.2 p hp q hq
end CompactCoreFinite

end

end OAI
