import Mathlib
import OAI.Combinatorics.UniformKServer.EpochAlphaJump

namespace OAI

                                       
section

/-! Parameter changes inside one actual held-vector epoch: sparse coordinates
when the held side reference is unchanged, side mass otherwise. -/
noncomputable section
namespace UniformKServer.EpochAlphaStatic
open Finset
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem dominant_base {s r : EpochGeometry.State ι} (h : s.base=r.base) :
    EpochGeometry.dominant s=EpochGeometry.dominant r := by
  unfold EpochGeometry.dominant
  rw [h]

theorem config_regular {s : EpochGeometry.State ι} {a : ι → ℝ}
    (hn : (EpochParameters.active a).Nonempty) (ho : EpochGeometry.dominant s=none)
    (U ell ct C : ℝ) : EpochAlphaSchedule.config a s U ell ct C=
      some (EpochAlpha.regular a (EpochGeometry.total s.base) ell ct C) := by
  simp only [EpochAlphaSchedule.config,ite_eq_left hn,ho]

theorem config_marked {s : EpochGeometry.State ι} {a : ι → ℝ} {o : ι}
    (hi : o ∈ EpochParameters.active a) (ho : EpochGeometry.dominant s=some o)
    {U ell ct C : ℝ} (hU : U ≠ 0) : EpochAlphaSchedule.config a s U ell ct C=
      some (EpochAlpha.marked a (EpochGeometry.total s.base) U ell ct C ⟨o,hi⟩) := by
  have hn : (EpochParameters.active a).Nonempty := ⟨o,hi⟩
  simp only [EpochAlphaSchedule.config,ite_eq_left hn,ho,dite_eq_left hi,ite_eq_right hU]

theorem config_singleton {s : EpochGeometry.State ι} {a : ι → ℝ} {o : ι}
    (hi : o ∈ EpochParameters.active a) (ho : EpochGeometry.dominant s=some o)
    (ell ct C : ℝ) : EpochAlphaSchedule.config a s 0 ell ct C=
      some (EpochAlpha.singleton a ell ct C ⟨o,hi⟩) := by
  have hn : (EpochParameters.active a).Nonempty := ⟨o,hi⟩
  simp only [EpochAlphaSchedule.config,ite_eq_left hn,ho,dite_eq_left hi,ite_true]

theorem singleton_zero (a B v : ι → ℝ) (ell ct C : ℝ)
    (o : EpochParameters.active a) :
    AdaptiveAlpha.potential (EpochAlpha.singleton a ell ct C o) B v=0 :=
  AlphaParameterChanges.singleton_potential o rfl B v

theorem nonempty_of_input {a B : ι → ℝ}
    (hs : DomainTransport.Supported (EpochParameters.active a) B)
    (hS : 0 < ∑ i, B i) : (EpochParameters.active a).Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  have hz : B=fun _ => 0 := by
    funext i
    exact hs i (by simp [he])
  simp only [hz,sum_const_zero,lt_self_iff_false] at hS

theorem marked_bound {a b B : ι → ℝ} {s : EpochGeometry.State ι}
    (ha : ∀ i, 0 ≤ a i) (hb : EpochGeometry.total b ≤ (101/100)*EpochGeometry.total s.base)
    {o : ι} (hi : o ∈ EpochParameters.active a) (ho : EpochGeometry.dominant s=some o)
    {U ell ct C : ℝ} (hU : EpochParameters.sideReference a o U) (hct : ct/ell ≤ 1)
    (hsc : 0 ≤ C*ell) (hp : AlphaEmpty.valid (EpochAlphaSchedule.config a s U ell ct C))
    (v : ι → ℝ) (hB : ∀ i, 0 ≤ B i) (hBb : ∀ i, B i ≤ 40*b i)
    (hs : DomainTransport.Supported (EpochParameters.active a) B)
    (hv : ∀ i, v i ∈ Set.Icc (0:ℝ) 1) (hsum : ∑ i, v i=1)
    (hf : ∀ i, (∑ j, B j)*v i ≤ 2*B i) :
    |AlphaEmpty.potential (EpochAlphaSchedule.config a s U ell ct C) B v| ≤
      (C*ell)*(520*EpochGeometry.side o b+246*EpochGeometry.side o a) := by
  by_cases hz : U=0
  · rw [hz,config_singleton hi ho]
    change |AdaptiveAlpha.potential (EpochAlpha.singleton a ell ct C ⟨o,hi⟩) B v| ≤ _
    rw [singleton_zero,abs_zero]
    have hbside : 0 ≤ EpochGeometry.side o b := by
      have h := EpochAlphaJump.side_input hBb o
      have h0 : 0 ≤ (∑ i, B i)-B o := by
        have hh := single_le_sum (s:=univ) (f:=B) (fun i _ => hB i) (mem_univ o)
        linarith
      linarith
    exact mul_nonneg hsc (by linarith [EpochParameters.side_nonneg ha o])
  · rw [config_marked hi ho hz] at hp ⊢
    exact EpochAlphaJump.marked_sized ha hb ⟨o,hi⟩ (EpochGeometry.dominant_spec ho).1
      hU hct hp v hB hBb hs hv hsum hf

theorem same_epoch {a b B : ι → ℝ} {s r : EpochGeometry.State ι}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hs : EpochGeometry.valid a s) (hr : EpochGeometry.valid b r) (he : s.base=r.base)
    {U V ell ct C : ℝ} (hsc : 0 ≤ C*ell) (hct : ct/ell ≤ 1)
    (hU : ∀ o, EpochGeometry.dominant s=some o → EpochParameters.sideReference a o U)
    (hV : ∀ o, EpochGeometry.dominant r=some o → EpochParameters.sideReference b o V)
    (hp : AlphaEmpty.valid (EpochAlphaSchedule.config a s U ell ct C))
    (hq : AlphaEmpty.valid (EpochAlphaSchedule.config b r V ell ct C))
    (v : ι → ℝ) (hS : 0 < ∑ i, B i) (hB : ∀ i, 0 ≤ B i)
    (hBb : ∀ i, B i ≤ 40*b i)
    (hpa : DomainTransport.Supported (EpochParameters.active a) B)
    (hqa : DomainTransport.Supported (EpochParameters.active b) B)
    (hv : ∀ i, v i ∈ Set.Icc (0:ℝ) 1) (hsum : ∑ i, v i=1)
    (hf : ∀ i, (∑ j, B j)*v i ≤ 2*B i) :
    |AlphaEmpty.potential (EpochAlphaSchedule.config b r V ell ct C) B v-
      AlphaEmpty.potential (EpochAlphaSchedule.config a s U ell ct C) B v| ≤
      8*(C*ell)*(∑ i, if a i=b i then 0 else B i)+
      (if U=V then 0 else match EpochGeometry.dominant s with
        | none => 0
        | some o => 1600*(C*ell)*(EpochGeometry.side o a+EpochGeometry.side o b)) := by
  have hna := nonempty_of_input hpa hS
  have hnb := nonempty_of_input hqa hS
  have hd := dominant_base he
  have hchg : 0 ≤ 8*(C*ell)*(∑ i, if a i=b i then 0 else B i) := by
    exact mul_nonneg (by positivity) (sum_nonneg fun i _ => by split_ifs; exact le_rfl; exact hB i)
  cases ho : EpochGeometry.dominant s with
  | none =>
    have ho' : EpochGeometry.dominant r=none := hd.symm.trans ho
    rw [config_regular hna ho] at hp
    rw [config_regular hnb ho'] at hq
    rw [config_regular hna ho,config_regular hnb ho']
    have h := EpochAlphaJump.regular hp (by simpa only [←he,AlphaEmpty.valid] using hq) B v hB hpa hqa hv hf
    simp only [AlphaEmpty.potential,←he,ho] at *
    split_ifs <;> simpa using h
  | some o =>
    have ho' : EpochGeometry.dominant r=some o := hd.symm.trans ho
    have hia := EpochAlphaSchedule.dominant_active hs ho
    have hib := EpochAlphaSchedule.dominant_active hr ho'
    by_cases hUV : U=V
    · rw [ite_eq_left hUV]
      rw [←hUV] at hq ⊢
      by_cases hz : U=0
      · rw [hz,config_singleton hia ho,config_singleton hib ho']
        simp only [AlphaEmpty.potential,singleton_zero,sub_self,abs_zero,add_zero]
        exact hchg
      · rw [config_marked hia ho hz] at hp
        rw [config_marked hib ho' hz] at hq
        rw [config_marked hia ho hz,config_marked hib ho' hz]
        have h := EpochAlphaJump.marked ⟨o,hia⟩ ⟨o,hib⟩ rfl hp
          (by simpa only [←he,AlphaEmpty.valid] using hq) B v hB hpa hqa hv hf
        simpa only [AlphaEmpty.potential,←he,add_zero] using h
    · simp only [ite_eq_right hUV]
      have ht := EpochAlphaJump.total_upper hr
      have hp' := marked_bound ha (by simpa only [he] using ht) hia ho (hU o ho) hct hsc hp
        v hB hBb hpa hv hsum hf
      have hq' := marked_bound hb ht hib ho' (hV o ho') hct hsc hq
        v hB hBb hqa hv hsum hf
      have hh := abs_sub (AlphaEmpty.potential (EpochAlphaSchedule.config b r V ell ct C) B v)
        (AlphaEmpty.potential (EpochAlphaSchedule.config a s U ell ct C) B v)
      have hsa := mul_nonneg hsc (EpochParameters.side_nonneg ha o)
      have hsb := mul_nonneg hsc (EpochParameters.side_nonneg hb o)
      nlinarith

end UniformKServer.EpochAlphaStatic

end


end

end OAI
