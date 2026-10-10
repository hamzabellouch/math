import OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy
import OAI.NumberTheory.DirichletL.Moments.UniformRadialComparison

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentCommonMaskRadialEnergy
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentRadialPolynomialEnergy
open CenteredMomentUniformReflectionProfile
local notation "O" => HeckeFamily.O

lemma naturalSlot_bounded (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    ∃B : ℝ,0≤B ∧ ∀χ : Character,‖naturalSlot χ pool β P‖≤B := by
  refine ⟨‖(Real.sqrt P:ℂ)⁻¹‖*∑I∈pool,‖β I‖,by positivity,?_⟩
  intro χ
  unfold naturalSlot
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)

lemma slots_bounded {α : Type*} (F : Finset α) (pool : α→Finset (Ideal O))
    (β : α→Ideal O→ℂ) (P : α→ℝ) :
    ∃B : ℝ,0≤B ∧ ∀χ : Character,‖∏j∈F,naturalSlot χ (pool j) (β j) (P j)‖≤B := by
  choose B hB hb using fun j=>naturalSlot_bounded (pool j) (β j) (P j)
  refine ⟨∏j∈F,B j,Finset.prod_nonneg (fun j _=>hB j),?_⟩
  intro χ
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun j _=>norm_nonneg _) (fun j _=>hb j χ)

theorem actual_radial_shared_energy {α : Type*} [DecidableEq α]
    (F : Finset α) (b M : α→ℝ) (hM : ∀j∈F,0≤M j) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)
      (χ : O→Character)(W₁ W₂ : 𝓢(ℝ,ℂ))(X₁ X₂ a₁ b₁ a₂ b₂ : ℝ)
      (pool : α→Finset (Ideal O))(β : α→Ideal O→ℂ)(P : α→ℝ)
      (keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K E : ℝ),
      0<X₁ → 0<X₂ → 0≤b₁ → 0≤b₂ →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      (∀j∈F,∀I∈pool j,Prime I) → (∀j∈F,0<P j) →
      (∀j∈F,∀I∈pool j,‖β j I‖≤M j) →
      (∀j∈F,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) →
      0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) → 0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        radialEnergy (fun z=>polynomial (χ z) false W₁
          (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          polynomial (χ z) false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j)) keep Φ K≤E) →
      radialEnergy (fun z=>polynomial ((χ z).excludePrimes R hR) false W₁ X₁ 0 0 *
        polynomial ((χ z).excludePrimes R hR) false W₂ X₂ 0 0 *
        ∏j∈F,naturalSlot ((χ z).excludePrimes R hR) (pool j) (β j) (P j)) keep Φ K≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E := by
  obtain ⟨C,hC,he⟩:=actual_shared_energy F b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro R hR χ W₁ W₂ X₁ X₂ a₁ b₁ a₂ b₂ pool β P keep Φ K E
    hX₁ hX₂ hb₁ hb₂ hs₁ hs₂ hp hP hβ hs hK hΦ hE hchild
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  let q (z : ↥S) : ℂ:=(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hh:=he R hR (fun z:↥S=>χ z) (fun z=>q z • W₁) (fun _=>W₂)
    (fun _=>X₁) (fun _=>X₂) (fun _=>pool) (fun _=>β) (fun _=>P)
    (fun _=>hX₁) (fun _=>hX₂) (fun _=>hp) (fun _=>hP)
    (fun _=>hβ) (fun _=>hs) E hE ?_
  · have hid (χ₀ : Character) (z : ↥S) (X : ℝ) :
        polynomial χ₀ false (q z • W₁ : 𝓢(ℝ,ℂ)) X 0 0=q z*polynomial χ₀ false W₁ X 0 0 := by
      exact polynomial_const_mul χ₀ W₁ X 0 0 (q z)
    simp_rw [hid] at hh
    have halg (z : ↥S) (u v w : ℂ) : q z*u*v*w=(u*v*w)*q z := by ring
    simp_rw [halg] at hh
    exact (finite_weighted rows keep _ Φ K hΦ).symm.trans_le hh
  · intro D₁ hD₁ D₂ hD₂ J hJ
    have hn (D : Finset (Ideal O)) (hD : D∈R.powerset) :
        0<(Ideal.absNorm (∏I∈D,I):ℝ) := by
      apply Nat.cast_pos.mpr
      exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun I hI=>(hR I (Finset.mem_powerset.mp hD hI)).ne_zero)))
    obtain ⟨PB,hPB,hbound⟩:=slots_bounded (F\J) pool β P
    have hsum:=pair_radial_summable χ
      (fun z=>∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j))
      (fun _=>0) (fun _=>0) W₁ W₂ a₁ b₁ a₂ b₂
      (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) PB
      hb₁ hb₂ (div_pos hX₁ (hn D₁ hD₁)) (div_pos hX₂ (hn D₂ hD₂)) hs₁ hs₂
      (fun z=>hbound (χ z)) keep Φ K hK
    have hid (χ₀ : Character) (z : ↥S) (X : ℝ) :
        polynomial χ₀ false (q z • W₁ : 𝓢(ℝ,ℂ)) X 0 0=q z*polynomial χ₀ false W₁ X 0 0 :=
      polynomial_const_mul χ₀ W₁ X 0 0 (q z)
    simp_rw [hid]
    have halg (z : ↥S) (u v w : ℂ) : q z*u*v*w=(u*v*w)*q z := by ring
    simp_rw [halg]
    dsimp only [q]
    rw [finite_weighted rows keep (fun z=>polynomial (χ z) false W₁
      (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
      polynomial (χ z) false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
      ∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j)) Φ K hΦ]
    exact (hsum.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)).trans
      (hchild D₁ hD₁ D₂ hD₂ J hJ)
end SevenEighths.CenteredMomentCommonMaskRadialEnergy

end

end OAI
