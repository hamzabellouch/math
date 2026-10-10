import OAI.Analysis.AncientFlat.Geometry.InteriorCore

namespace OAI
noncomputable section
open Set Filter
namespace ParabolicInterior
variable {V : Type} [NormedAddCommGroup V]
variable {E : Type*} [NormedAddCommGroup E]
def semiValues (α : ℝ) (Ω : Set (V × ℝ)) (f : V × ℝ → E) : Set ℝ :=
  {v | v=0 ∨ ∃ p∈Ω, ∃ z∈Ω, v=‖f p-f z‖/pdist p z^α}
def seminorm (α : ℝ) (Ω : Set (V × ℝ)) (f : V × ℝ → E) : ℝ :=
  sSup (semiValues α Ω f)
lemma zero_mem_semiValues (α : ℝ) (Ω : Set (V × ℝ)) (f : V × ℝ → E) :
    0∈semiValues α Ω f := Or.inl rfl
lemma semiValues_bounded {α M : ℝ} {Ω : Set (V × ℝ)} {f : V × ℝ → E} (hM : 0≤M)
    (hh : ∀ p∈Ω, ∀ z∈Ω, ‖f p-f z‖≤M*pdist p z^α) :
    ∀ v∈semiValues α Ω f, v≤M := by
  intro v hv
  rcases hv with rfl | ⟨p,hp,z,hz,rfl⟩
  · exact hM
  have hd : 0≤pdist p z^α := Real.rpow_nonneg (by unfold pdist; positivity) _
  rcases eq_or_lt_of_le hd with hd | hd
  · simp only [←hd,div_zero]; exact hM
  · exact (div_le_iff₀ hd).mpr (hh p hp z hz)
lemma seminorm_le {α M : ℝ} {Ω : Set (V × ℝ)} {f : V × ℝ → E} (hM : 0≤M)
    (hh : ∀ p∈Ω, ∀ z∈Ω, ‖f p-f z‖≤M*pdist p z^α) : seminorm α Ω f≤M :=
  csSup_le ⟨0,zero_mem_semiValues α Ω f⟩ (semiValues_bounded hM hh)
lemma seminorm_nonneg {α M : ℝ} {Ω : Set (V × ℝ)} {f : V × ℝ → E} (hM : 0≤M)
    (hh : ∀ p∈Ω, ∀ z∈Ω, ‖f p-f z‖≤M*pdist p z^α) : 0≤ seminorm α Ω f :=
  le_csSup ⟨M,semiValues_bounded hM hh⟩ (zero_mem_semiValues α Ω f)
lemma seminorm_bound {α M : ℝ} {Ω : Set (V × ℝ)} {f : V × ℝ → E} (hM : 0≤M)
    (hh : ∀ p∈Ω, ∀ z∈Ω, ‖f p-f z‖≤M*pdist p z^α) :
    ∀ p∈Ω, ∀ z∈Ω, ‖f p-f z‖≤ seminorm α Ω f*pdist p z^α := by
  intro p hp z hz
  have hd : 0≤pdist p z^α := Real.rpow_nonneg (by unfold pdist; positivity) _
  rcases eq_or_lt_of_le hd with hd | hd
  · have hh := hh p hp z hz
    rw [←hd,mul_zero] at hh ⊢
    exact hh
  · apply (div_le_iff₀ hd).mp
    exact le_csSup ⟨M,semiValues_bounded hM hh⟩ (Or.inr ⟨p,hp,z,hz,rfl⟩)
end ParabolicInterior

end

end OAI
