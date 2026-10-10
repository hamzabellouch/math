import OAI.NumberTheory.DirichletL.Energy.OriginalSource

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyFixedRadialSource
open HeckeFamily CenteredMomentSourceRow CenteredMomentAbsoluteEnergy CenteredMomentHeckeExpansion
open QuadraticInitialBound ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

lemma norm_le_diagonalControl (Φ:𝓢(ℝ,ℂ))(x:ℝ):‖Φ x‖≤diagonalControl Φ:=by
  have hs:SchwartzMap.seminorm ℝ 0 0 Φ≤
      (Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ:=by
    exact Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ)
      (by simp : (0,0)∈Finset.Iic (2,0))) Φ
  apply (SchwartzMap.norm_le_seminorm ℝ Φ x).trans
  apply hs.trans
  unfold diagonalControl
  exact le_mul_of_one_le_left (by positivity) (by nlinarith [Real.pi_nonneg])

theorem exists_fixed_bump (b:ℝ)(_hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ (∀x,(Ψ x).im=0) ∧
      (∀x∈Set.Icc (0:ℝ) b,Ψ x=1):=by
  have hsub:Set.Icc (0:ℝ) b⊆Set.Ioo (-1) (b+1):=by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  obtain ⟨f,hf,_,hs,hone⟩:=exists_contDiff_support_eq_eq_one_iff
    (n:=⊤) isOpen_Ioo isClosed_Icc hsub
  let v:ℝ→ℂ:=fun x=>((f x)^2:ℝ)
  have hv:ContDiff ℝ ∞ v:=Complex.ofRealCLM.contDiff.comp
    ((by simpa using hf:ContDiff ℝ ∞ f).pow 2)
  have hsupp:Function.support v⊆Set.Icc (-1) (b+1):=by
    intro x hx
    have hn:x∈Function.support f:=by
      intro hz
      exact hx (by simp [v,hz])
    rw [hs] at hn
    exact ⟨hn.1.le,hn.2.le⟩
  let Ψ:𝓢(ℝ,ℂ):=(HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp).toSchwartzMap hv
  refine ⟨Ψ,hsupp,?_,?_,?_⟩
  · intro x
    change 0≤(f x)^2
    positivity
  · intro x
    exact Complex.ofReal_im _
  · intro x hx
    change (((f x)^2:ℝ):ℂ)=1
    rw [(hone x).mp hx]
    norm_num

theorem finite_energy_domination (b:ℝ)(Ψ:𝓢(ℝ,ℂ))
    (hΨ:∀x,0≤(Ψ x).re)(hone:∀x∈Set.Icc (0:ℝ) b,Ψ x=1)
    (Φ:𝓢(ℝ,ℂ))(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic b)
    (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (K:ℝ)(hK:0<K):
    ‖finiteHeckeEnergy η m A t S c Φ K‖≤
      diagonalControl Φ*‖finiteHeckeEnergy η m A t S c Ψ K‖:=by
  have hΦ:∀x:ℝ,0≤x→‖Φ x‖≤diagonalControl Φ*(Ψ x).re:=by
    intro x hx
    by_cases h:Φ x=0
    · rw [h,norm_zero]
      exact mul_nonneg (diagonalControl_nonneg Φ) (hΨ x)
    · rw [hone x ⟨hx,hs h⟩,Complex.one_re,mul_one]
      exact norm_le_diagonalControl Φ x
  have hsumΦ:=finite_hecke_energy_summable η m A t S c Φ K hK
  have hsumΨ:=finite_hecke_energy_summable η m A t S c Ψ K hK
  have hre:HasSum (fun z:O=>‖∑I∈S,c I*rowWeight η m A z t I‖^2*
      (Ψ (‖eisEmbedding z‖^2/K)).re)
      (finiteHeckeEnergy η m A t S c Ψ K).re:=by
    have hh:=Complex.hasSum_re hsumΨ.hasSum
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
      finiteHeckeEnergy] using hh
  calc
    _≤∑'z:O,‖((‖∑I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
      Φ (‖eisEmbedding z‖^2/K)‖:=norm_tsum_le_tsum_norm hsumΦ.norm
    _≤∑'z:O,diagonalControl Φ*(‖∑I∈S,c I*rowWeight η m A z t I‖^2*
      (Ψ (‖eisEmbedding z‖^2/K)).re):=by
      apply hsumΦ.norm.tsum_le_tsum _ (hre.summable.mul_left _)
      intro z
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact (mul_le_mul_of_nonneg_left (hΦ _ (by positivity)) (sq_nonneg _)).trans_eq (by ring)
    _=diagonalControl Φ*(finiteHeckeEnergy η m A t S c Ψ K).re:=by
      rw [tsum_mul_left,hre.tsum_eq]
    _≤_:=mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (diagonalControl_nonneg Φ)

theorem fixed_source (b:ℝ)(hb:0<b):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (b+1) ∧
      (∀x,0≤(Ψ x).re) ∧ ∀Φ:𝓢(ℝ,ℂ),Function.support (Φ:ℝ→ℂ)⊆Set.Iic b→
      ∀(η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)(K:ℝ),0<K→
      ‖finiteHeckeEnergy η m A t S c Φ K‖≤
        diagonalControl Φ*‖finiteHeckeEnergy η m A t S c Ψ K‖:=by
  obtain ⟨Ψ,hs,hn,_,hone⟩:=exists_fixed_bump b hb
  exact ⟨Ψ,hs,hn,fun Φ hΦ η m A t S c K hK=>finite_energy_domination b Ψ hn hone Φ hΦ η m A t S c K hK⟩

end SevenEighths.CenteredMomentEnergyFixedRadialSource

end

end OAI
