import OAI.Analysis.AncientFlat.Weighted.ExactYNorm
import OAI.Analysis.AncientFlat.Weighted.WeightedEstimateCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ENNReal
namespace FlatWeighted
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def jetComponent {m : ℕ} (e : OrthonormalBasis (Fin m) ℝ V) (j : ℕ)
    (i : Fin j → Fin m) (u : ℝ → V → ℂ) (p : V × ℝ) : ℂ :=
  iteratedFDeriv ℝ j (u p.2) p.1 (fun k => e (i k))
def localXNorm {m : ℕ} (e : OrthonormalBasis (Fin m) ℝ V) (α : ℝ) (Ω : Set (V × ℝ))
    (u ut : ℝ → V → ℂ) : ℝ≥0∞ :=
  (∑ j : Fin 5, ∑ i : Fin j.val → Fin m, holderNorm α Ω (jetComponent e j.val i u))+
    holderNorm α Ω (fun p => ut p.2 p.1)
def xNorm {m : ℕ} (e : OrthonormalBasis (Fin m) ℝ V) (α w a : ℝ)
    (u ut : ℝ → V → ℂ) : ℝ≥0∞ :=
  ⨆ p : {p : V × ℝ // p.2<0}, localXNorm e α (localDomain a p.val)
    (weightedValue w p.val u) (weightedTime w p.val ut)
omit [InnerProductSpace ℝ V] in
lemma holderBound_holderNorm {α M : ℝ} {Ω : Set (V × ℝ)} {f : V × ℝ → ℂ}
    (hM : 0≤M) (h : HolderBound α Ω f M) : holderNorm α Ω f≤ENNReal.ofReal (2*M) := by
  classical
  have hs : (⨆ p∈Ω, ‖f p‖ₑ)≤ENNReal.ofReal M := by
    apply iSup₂_le
    intro p hp
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (h.1 p hp)
  have hh : (⨆ p∈Ω, ⨆ q∈Ω, if p=q then 0 else ‖f p-f q‖ₑ/ENNReal.ofReal (pdist p q^α))≤ENNReal.ofReal M := by
    apply iSup₂_le
    intro p hp
    apply iSup₂_le
    intro q hq
    split_ifs with he
    · exact bot_le
    · have hd : 0<pdist p q^α := Real.rpow_pos_of_pos (pdist_pos_of_ne he) _
      apply (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr hd) ENNReal.ofReal_ne_top).mpr
      simpa only [ofReal_norm,←ENNReal.ofReal_mul hM] using ENNReal.ofReal_le_ofReal (h.2 p hp q hq)
  unfold holderNorm
  exact (add_le_add hs hh).trans_eq (by rw [←ENNReal.ofReal_add hM hM]; congr 1; ring)
lemma component_holder {m j : ℕ} (e : OrthonormalBasis (Fin m) ℝ V) (i : Fin j → Fin m)
    {α M : ℝ} {Ω : Set (V × ℝ)} {u : ℝ → V → ℂ}
    (h : HolderBound α Ω (fun p => iteratedFDeriv ℝ j (u p.2) p.1) M) :
    HolderBound α Ω (jetComponent e j i u) M := by
  have hEval (f : V [×j]→L[ℝ] ℂ) : ‖f (fun k => e (i k))‖≤‖f‖ := by
    have hh := f.le_opNorm (fun k => e (i k))
    simpa only [e.norm_eq_one,Finset.prod_const_one,mul_one] using hh
  constructor
  · intro p hp
    exact (hEval _).trans (h.1 p hp)
  · intro p hp q hq
    change ‖iteratedFDeriv ℝ j (u p.2) p.1 (fun k => e (i k))-iteratedFDeriv ℝ j (u q.2) q.1 (fun k => e (i k))‖≤_
    rw [←sub_apply]
    exact (hEval _).trans (h.2 p hp q hq)
lemma jetBound_localXNorm {m : ℕ} (e : OrthonormalBasis (Fin m) ℝ V)
    {α M : ℝ} {Ω : Set (V × ℝ)} {u ut : ℝ → V → ℂ} (hM : 0≤M)
    (h : JetBound α Ω u ut M) :
    localXNorm e α Ω u ut≤ENNReal.ofReal ((2*((∑ j : Fin 5, (m:ℝ)^j.val)+1))*M) := by
  have hs : (∑ j : Fin 5, ∑ i : Fin j.val → Fin m, holderNorm α Ω (jetComponent e j.val i u))≤
      ∑ j : Fin 5, ∑ i : Fin j.val → Fin m, ENNReal.ofReal (2*M) := by
    apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro i hi
    exact holderBound_holderNorm hM (component_holder e i (h.1 j.val (by omega)))
  have ht := holderBound_holderNorm hM h.2
  unfold localXNorm
  apply (add_le_add hs ht).trans_eq
  have h2M : 0≤2*M := by positivity
  have hh (j : Fin 5) : (∑ i : Fin j.val → Fin m, ENNReal.ofReal (2*M)) =
      ENNReal.ofReal ((m:ℝ)^j.val*(2*M)) := by
    rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => h2M)]
    congr 1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul]
    push_cast
    rfl
  simp_rw [hh]
  rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  rw [←ENNReal.ofReal_add (by positivity) h2M]
  congr 1
  simp only [←Finset.sum_mul]
  ring
lemma xBound_xNorm {m : ℕ} (e : OrthonormalBasis (Fin m) ℝ V)
    {α w a M : ℝ} {u ut : ℝ → V → ℂ} (hM : 0≤M) (h : XBound α w a M u ut) :
    xNorm e α w a u ut≤ENNReal.ofReal ((2*((∑ j : Fin 5, (m:ℝ)^j.val)+1))*M) := by
  apply iSup_le
  intro p
  exact jetBound_localXNorm e hM (h p.val p.property)
end FlatWeighted

end

end OAI
