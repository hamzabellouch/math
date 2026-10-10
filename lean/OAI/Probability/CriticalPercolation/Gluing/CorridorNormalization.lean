import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.CorridorGraph
import OAI.Probability.CriticalPercolation.Gluing.RelayMoves

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open BondGraph

variable {V : Type*}

def timeCenter (T : ℝ) (v : Site) : ℝ := ((v.1 : ℝ)+v.2)*T
def heightCenter (T : ℝ) (v : Site) : ℝ := ((v.1 : ℝ)-v.2)*T/4
def normalized (t z : V → ℝ) (T : ℝ) : V → Point := fun x => (t x/T,4*z x/T)
def localTime (t : V → ℝ) (T : ℝ) (v : Site) : V → ℝ := fun x => t x-timeCenter T v
def localHeight (z : V → ℝ) (T : ℝ) (v : Site) : V → ℝ := fun x => z x-heightCenter T v
def sign (b : Bool) : ℝ := if b then 1 else -1

def mark (t z : V → ℝ) (T ρ : ℝ) (v : Site) : Set V :=
  {x | 0≤localTime t T v x ∧ localTime t T v x≤ρ ∧ |localHeight z T v x|≤210}

lemma sign_abs (b : Bool) : |sign b|=1 := by cases b <;> norm_num [sign]

lemma timeCenter_target (T : ℝ) (v : Site) (b : Bool) :
    timeCenter T (target (v,b))=timeCenter T v+T := by
  cases b <;> simp [target,timeCenter] <;> ring

lemma heightCenter_target (T : ℝ) (v : Site) (b : Bool) :
    heightCenter T (target (v,b))=heightCenter T v+sign b*T/4 := by
  cases b <;> simp [target,heightCenter,sign] <;> ring

lemma normalized_box (t z : V → ℝ) (T J : ℝ) (hT : 0<T) (v : Site) :
    graphBox (normalized t z T) (J/T) (2520/T) v=
      {x | |localTime t T v x|≤J ∧ |localHeight z T v x|≤J/4+630} := by
  ext x
  change (|t x/T-((v.1 : ℝ)+v.2)|≤J/T ∧
    |4*z x/T-((v.1 : ℝ)-v.2)|≤J/T+2520/T) ↔ _
  have ht : t x/T-((v.1 : ℝ)+v.2)=localTime t T v x/T := by
    dsimp [localTime,timeCenter]; field_simp
  have hz : 4*z x/T-((v.1 : ℝ)-v.2)=4*localHeight z T v x/T := by
    dsimp [localHeight,heightCenter]; field_simp
  rw [ht,hz,abs_div,abs_div,abs_of_pos hT,div_le_div_iff_of_pos_right hT,
    show J/T+2520/T=(J+2520)/T by ring,div_le_div_iff_of_pos_right hT,
    abs_mul,show |(4 : ℝ)|=4 by norm_num]
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor <;> rintro ⟨ht,hz⟩ <;> exact ⟨ht,by linarith⟩

lemma normalized_tube (t z : V → ℝ) (T : ℝ) (hT : 0<T) (v : Site) (b : Bool) :
    (normalized t z T) ⁻¹' tube (2520/T) (v,b)=
      {x | 0≤localTime t T v x ∧ localTime t T v x≤T ∧
        |localHeight z T v x-sign b*localTime t T v x/4|≤630} := by
  ext x
  have ht : ((v.1 : ℝ)+v.2≤t x/T) ↔ 0≤localTime t T v x := by
    rw [le_div_iff₀ hT]; dsimp [localTime,timeCenter]; constructor <;> intro h <;> linarith
  have ht' : (t x/T≤(v.1 : ℝ)+v.2+1) ↔ localTime t T v x≤T := by
    rw [div_le_iff₀ hT]; dsimp [localTime,timeCenter]; constructor <;> intro h <;> nlinarith
  cases b with
  | true =>
    change (((v.1 : ℝ)+v.2≤t x/T) ∧ (t x/T≤(v.1 : ℝ)+v.2+1) ∧
      |4*z x/T-(t x/T-2*(v.2 : ℝ))|≤2520/T) ↔ _
    have he : 4*z x/T-(t x/T-2*(v.2 : ℝ))=
        4*(localHeight z T v x-sign true*localTime t T v x/4)/T := by
      dsimp [localHeight,heightCenter,localTime,timeCenter,sign]; field_simp; ring
    rw [ht,ht',he,abs_div,abs_of_pos hT,div_le_div_iff_of_pos_right hT,
      abs_mul,show |(4 : ℝ)|=4 by norm_num]
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    constructor <;> rintro ⟨ha,hb,hc⟩ <;> exact ⟨ha,hb,by linarith⟩
  | false =>
    change (((v.1 : ℝ)+v.2≤t x/T) ∧ (t x/T≤(v.1 : ℝ)+v.2+1) ∧
      |4*z x/T-(2*(v.1 : ℝ)-t x/T)|≤2520/T) ↔ _
    have he : 4*z x/T-(2*(v.1 : ℝ)-t x/T)=
        4*(localHeight z T v x-sign false*localTime t T v x/4)/T := by
      dsimp [localHeight,heightCenter,localTime,timeCenter,sign]; field_simp; ring
    rw [ht,ht',he,abs_div,abs_of_pos hT,div_le_div_iff_of_pos_right hT,
      abs_mul,show |(4 : ℝ)|=4 by norm_num]
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    constructor <;> rintro ⟨ha,hb,hc⟩ <;> exact ⟨ha,hb,by linarith⟩

lemma normalized_domain (t z : V → ℝ) (T J : ℝ) (hT : 0<T) (v : Site) (b : Bool) :
    graphDomain (normalized t z T) (J/T) (2520/T) (v,b)=
      relayDomain (localTime t T v) (localHeight z T v) J T (sign b) := by
  change (normalized t z T) ⁻¹' (box _ _ v∪box _ _ (target (v,b))∪tube _ (v,b))=_
  rw [Set.preimage_union,Set.preimage_union]
  change graphBox _ _ _ v∪graphBox _ _ _ (target (v,b))∪_=_
  rw [normalized_box t z T J hT,normalized_box t z T J hT,normalized_tube t z T hT]
  ext x
  change ((_ ∧ _) ∨ (_ ∧ _)) ∨ (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∨ (_ ∧ _)) ∨ (_ ∧ _ ∧ _)
  simp only [localTime,localHeight,timeCenter_target,heightCenter_target,sub_add_eq_sub_sub]

lemma mark_initial (t z : V → ℝ) (T ρ : ℝ) (v : Site) (b : Bool) :
    relayMark (localTime t T v) (localHeight z T v) 0 (sign b) ρ=mark t z T ρ v := by
  ext x
  simp only [relayMark,mark,Set.mem_ofPred_eq,mul_zero,zero_div,sub_zero,zero_add]

lemma mark_target (t z : V → ℝ) (T ρ : ℝ) (v : Site) (b : Bool) :
    relayMark (localTime t T v) (localHeight z T v) T (sign b) ρ=mark t z T ρ (target (v,b)) := by
  ext x
  change (T≤localTime t T v x ∧ localTime t T v x≤T+ρ ∧
    |localHeight z T v x-sign b*T/4|≤210) ↔ _
  change _ ↔ (0≤localTime t T (target (v,b)) x ∧ localTime t T (target (v,b)) x≤ρ ∧
    |localHeight z T (target (v,b)) x|≤210)
  simp only [localTime,localHeight,timeCenter_target,heightCenter_target]
  have he : z x-heightCenter T v-sign b*T/4=z x-(heightCenter T v+sign b*T/4) := by ring
  rw [he]
  constructor <;> rintro ⟨ha,hb,hc⟩ <;> exact ⟨by linarith,by linarith,hc⟩

lemma mark_subset_box (t z : V → ℝ) (T J ρ : ℝ) (hT : 0<T) (hJ : 0≤J) (hρJ : ρ≤J) (v : Site) :
    mark t z T ρ v⊆graphBox (normalized t z T) (J/T) (2520/T) v := by
  rw [normalized_box t z T J hT]
  intro x hx
  exact ⟨by rw [abs_of_nonneg hx.1]; exact hx.2.1.trans hρJ,by linarith [hx.2.2]⟩

lemma coordinateMove_translate {E : Type*} (G : BondGraph V E) (t z : V → ℝ)
    (T : ℝ) (v : Site) (m : ℕ) (e : ℝ) (y : V) (s : ℝ) :
    G.coordinateMove (localTime t T v) (localHeight z T v) m e y s=
      G.coordinateMove t z m e y s := by
  unfold coordinateMove localTime localHeight
  simp only [sub_sub_sub_cancel_right]
  have ht : ∀ b, t b-timeCenter T v-(t y-timeCenter T v+1)=t b-(t y+1) := by intro b; ring
  have hz : ∀ b, z b-heightCenter T v-(z y-heightCenter T v+s)=z b-(z y+s) := by intro b; ring
  simp only [ht,hz]

end CriticalPercolation.Corridor
end
end
end

end OAI
