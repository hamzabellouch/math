import OAI.MathematicalPhysics.Heisenberg.AveragedEnergy

namespace OAI

section
noncomputable section
open Filter Topology
open scoped RealInnerProductSpace Classical

noncomputable section
open scoped Classical BigOperators
namespace Heisenberg.Hitting
variable {V : Type*} [Fintype V]
lemma hitting_zero_column {U : Matrix V V ℝ} (hU : DoublySubstochastic U)
    (T : Finset V) {i : V} (hi : i ∉ T) (hz : ∀ j, U j i = 0) :
    hitting U T i = 0 := by
  rw [←hitting_harmonic hU T hi]
  simp [backward,hz]
end Heisenberg.Hitting

namespace Heisenberg.Exposure
open Heisenberg.Serial Heisenberg.Hitting Heisenberg.MeshPair Heisenberg.Cycle
variable {V : Type*} [Fintype V] [DecidableEq V]

def cutFactors (n : ℕ) (a b : Fin (n+1) → V) (p : Fin (n+1) → ℝ)
    (P : Set (Fin (n+1)×V)) (D : (Fin (n+1) → Bool) → Fin (n+1) → Set V)
    (base : Fin (n+1) → Bool) (i : Fin (n+1)) : Matrix V V ℝ :=
  residualBetween (D base i) (D base (finRotate (n+1) i))
    (layerRevealed (fun j => Equiv.swap (a j) (b j))
      (MissingSet (layerHistory (finRotate (n+1)) (fun j => Equiv.swap (a j) (b j)) base) P) i)
    (base i) (a i) (b i) (p i)

lemma cutFactors_substochastic (n : ℕ) (a b : Fin (n+1) → V) (p : Fin (n+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (P : Set (Fin (n+1)×V))
    (D : (Fin (n+1) → Bool) → Fin (n+1) → Set V) (base : Fin (n+1) → Bool) :
    ∀ i, Heisenberg.Hitting.DoublySubstochastic (cutFactors n a b p P D base i) := by
  intro i
  have h := residualBetween_substochastic (D base i) (D base (finRotate (n+1) i))
    (layerRevealed (fun j => Equiv.swap (a j) (b j))
      (MissingSet (layerHistory (finRotate (n+1)) (fun j => Equiv.swap (a j) (b j)) base) P) i)
    (base i) (a i) (b i) (p i) (hp i).1 (hp i).2
  exact ⟨h.nonneg,h.row,h.col⟩

theorem cut_return_energy (n : ℕ) (a b : Fin (n+1) → V) (p : Fin (n+1) → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (P : Set (Fin (n+1)×V))
    (D : (Fin (n+1) → Bool) → Fin (n+1) → Set V) (I : Set V)
    (T : Finset P) (T₀ : Finset V) (himage : T.image Subtype.val = cutTargets n T₀)
    (hT : ∀ base j, j∈T → j.val.2∈D base j.val.1)
    (hQ : ∀ base, (MissingSet
      (layerHistory (finRotate (n+1)) (fun j => Equiv.swap (a j) (b j)) base) P)ᶜ∩Pᶜ
      ⊆ {z | z.2∈D base z.1})
    (hI : ∀ base, D base 0 ⊆ I) :
    let τ := fun j => Equiv.swap (a j) (b j)
    let μ₀ := productWeight (fun i z => if z then p i else 1-p i)
    let μ := fun c => μ₀ c*(2:ℝ)^missingCount (layerHistory (finRotate (n+1)) τ c) P
    let θ := fun c => μ c/(∑ b,μ b)
    ∃ f : (Fin (n+1) → Bool) → V → ℝ,
      (∀ base j, 0 ≤ f base j ∧ f base j ≤ 1) ∧
      (∀ base j, j∈T₀ → f base j = 1) ∧
      (∀ base j, j∉I → f base j = 0) ∧
      (∑ c, θ c*returnCount (layerHistory (finRotate (n+1)) τ c) P T) ≤ (T₀.card:ℝ)-
        ∑ base, θ base*energy (product (n+1) (cutFactors n a b p P D base)) (f base) := by
  dsimp only
  let K := cutFactors n a b p P D
  let F := fun base => hitting (cyclicKernel n (K base)) (cutTargets n T₀)
  have hK := cutFactors_substochastic n a b p hp P D
  have hU := fun base => cyclicKernel_substochastic n (K base) (hK base)
  have hTb (base : Fin (n+1) → Bool) {j : V} (hj : j∈T₀) : j∈D base 0 := by
    have ht : (0,j)∈T.image Subtype.val := by rw [himage]; simp [mem_cutTargets,hj]
    obtain ⟨t,ht,he⟩ := Finset.mem_image.mp ht
    have hh := hT base t ht
    simpa only [he] using hh
  refine ⟨fun base j => F base (0,j), ?_, ?_, ?_, ?_⟩
  · intro base j
    exact ⟨(hitting_bounds (hU base) (cutTargets n T₀)).1 _,
      (hitting_bounds (hU base) (cutTargets n T₀)).2 _⟩
  · intro base j hj
    exact hitting_on (hU base) (cutTargets n T₀) (by simp [mem_cutTargets,hj])
  · intro base j hj
    have hD : j∉D base 0 := fun h => hj (hI base h)
    apply hitting_zero_column (hU base) (cutTargets n T₀)
    · simp only [mem_cutTargets,true_and]
      exact fun ht => hD (hTb base ht)
    · intro z
      simp only [cyclicKernel]
      split_ifs
      · dsimp [K,cutFactors]
        simp only [residualBetween]
        split_ifs <;> simp [killedBetween,hD,Matrix.add_apply,Matrix.smul_apply]
      · rfl
  · have hh := averaged_layer_energy (finRotate (n+1)) a b p hp P
      (fun base => {z | z.2∈D base z.1}) T hT hQ
    dsimp only at hh
    have hc : T.card=T₀.card := by
      have h := congrArg Finset.card himage
      rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
      simpa [cutTargets,Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)] using h
    rw [hc] at hh
    convert hh using 2
    congr 1
    ext base
    congr 1
    rw [killed_residual_cyclic,himage]
    exact (cyclic_hitting_energy n (K base) (hK base) T₀).symm

end Heisenberg.Exposure

end
end

noncomputable section
open scoped BigOperators Classical RealInnerProductSpace
namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.LatticeRegular Heisenberg.RoutedFlow Heisenberg.SpatialFrame
open Heisenberg.MeshPair Heisenberg.Exposure
variable {k : ℕ}

theorem exposed_prefix_leakage (hk : 2≤k) (L : ℝ) (hL : 0≤L) :
    ∃ M : ℕ,∃ C≥0,∀ (T B : Type) [Fintype T] [Fintype B] [Nonempty B]
      (Λ F : Finset (ZSite k)) (s : Equiv.Perm T)
      (a b : T → Slots (B:=B) Λ) (p : T → ℝ)
      (_hp : ∀ i,0≤p i ∧ p i≤1) (pins : Set (T×Slots (B:=B) Λ))
      (r : ℕ → T) (c : ℕ → ℕ) (J : Finset (Slots (B:=B) Λ))
      (f : (T → Bool) → EuclideanSpace ℝ (Slots (B:=B) Λ))
      (a₀ b₀ : ℕ → Slots (B:=B) Λ) (q n R : ℕ) (e : Fin q ≃ Edges Step Λ)
      (δ ρ ζ rem : ℝ),
      0<n → 0<δ → 0≤rem → (∀ j,r (j+1)=s (r j)) →
      (∀ i : Fin q,a₀ i=(e i).val.1) → (∀ i : Fin q,b₀ i=(e i).val.2) →
      F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
      (∀ base j,j∈J → j∈holeCut s (fun i=>Equiv.swap (a i) (b i)) base pins (r 0) ∧ j.1.val∈F) →
      (∀ base j,j∈J → (f base).ofLp j=1) →
      (∀ base j,0≤(f base).ofLp j ∧ (f base).ofLp j≤1) →
      (∀ base j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base pins (r 0)∩{j | j.1.val∈F} →
        (f base).ofLp j=0) →
      (∀ z u,0≤u → ((Finset.univ.filter (fun j : J=>dist j.val.1.val z≤u)).card:ℝ)≤
        L*(1+u)^((1:ℝ)/100)) →
      (∀ (i : Fin n) (j : J), (∑ base, Exposure.layerMass s a b pins p base *
        (if ¬Regular (blocked Λ (holeCut s (fun l=>Equiv.swap (a l) (b l)) base pins (r (c i))))
          j.val.1.val R M (1/(100*(k+1:ℝ))) then (1:ℝ) else 0))≤ρ) →
      (∀ (i : Fin n) (j : J), (∑ base,Exposure.layerMass s a b pins p base *
        (∑ v,if (R:ℝ)<dist v.1.val j.val.1.val then
          prefixMatrix (fun l=>exposedStep s a b base pins {v | v.1.val∈F} p (r l)) (c i) v j.val else 0))≤ζ) →
      (∀ i : Fin n,2*δ*(∑ base,Exposure.layerMass s a b pins p base *
        MeshPair.quietEnergy (holeCut s (fun l=>Equiv.swap (a l) (b l)) base pins (r (c i)))
          a₀ b₀ q (exposedSweep s a b base pins {v | v.1.val∈F} p r (c i) (f base)))≤
        (∑ base,Exposure.layerMass s a b pins p base *
          (‖exposedSweep s a b base pins {v | v.1.val∈F} p r (c i) (f base)‖^2-
            ‖exposedSweep s a b base pins {v | v.1.val∈F} p r (c (i+1)) (f base)‖^2))+rem) →
      (J.card:ℝ)-2*((ρ+ζ)*J.card)-
        2*(C*(1+(R:ℝ))^((1:ℝ)/100)*J.card)/(δ*(n:ℝ))-(n:ℝ)*rem ≤
      ∑ base,Exposure.layerMass s a b pins p base *
        (‖f base‖^2-‖exposedSweep s a b base pins {v | v.1.val∈F} p r (c n) (f base)‖^2) := by
  obtain ⟨M,C,hC,hh⟩ := routed_mean_leakage hk L hL
  refine ⟨M,C,hC,?_⟩
  intro T B _ _ _ Λ F s a b p hp pins r c J f a₀ b₀ q n R e δ ρ ζ rem hn hδ hrem
    hr ha hb hF hframe hJ hfJ hf hs hg hbad hesc hloss
  let I : Set (Slots (B:=B) Λ) := {v | v.1.val∈F}
  let H : (T → Bool) → ℕ → Set (Slots (B:=B) Λ) :=
    fun base i=>holeCut s (fun l=>Equiv.swap (a l) (b l)) base pins (r (c i))
  let A : (T → Bool) → ℕ → Matrix (Slots (B:=B) Λ) (Slots (B:=B) Λ) ℝ :=
    fun base i=>prefixMatrix (fun l=>exposedStep s a b base pins I p (r l)) (c i)
  let P := fun base i=>euclideanMap (A base i)
  let K := fun base i v (j : J)=>A base i v j.val
  let eta := indicatorVector J
  let g := fun base=>f base-eta
  have heq (base : T → Bool) : eta+g base=f base := by simp [g]
  have hA (base : T → Bool) (i : ℕ) : MatrixContraction.DoublySubstochastic (A base i) :=
    prefix_substochastic _ _ (fun l _=>exposedStep_substochastic s a b base pins I p hp (r l))
  have hPf (base : T → Bool) (i : ℕ) : P base i (eta+g base)=
      exposedSweep s a b base pins I p r (c i) (f base) := by
    rw [heq,exposedSweep_prefix]
  have hsupp (base : T → Bool) (i : ℕ) := exposedSweep_supported s a b base pins I p r (c i)
    (fun j _=>hr j) (f base) (hs base)
  have hnorm (base : T → Bool) (i : ℕ) (v : EuclideanSpace ℝ (Slots (B:=B) Λ)) :
      ‖P base i v‖≤‖v‖ := by
    change ‖euclideanMap (A base i) v‖≤‖v‖
    exact euclideanMap_contraction _ (hA base i) v
  have h := hh (T → Bool) J B Λ F H (fun j : J=>j.val.1.val) R
    (Exposure.layerMass s a b pins p) eta g P K a₀ b₀ q n e δ ρ ζ rem hn hδ hrem ha hb hF hframe
    (layerMass_nonneg s a b pins p hp) (layerMass_sum s a b pins p hp)
    (fun base=>indicatorVector_orth J (f base) (hfJ base))
    (fun base i _=>hnorm base i)
    (by
      intro base i j hj
      rw [hPf]
      exact hsupp base i j (fun h=>hj h.2))
    (by
      intro base i
      rw [hPf]
      exact exposedSweep_bounds s a b base pins I p hp r (c i) (f base) (hf base))
    (fun base i v j=>(hA base i).nonneg v j.val)
    (fun base i j=>(hA base i).col j.val) hg
    (by
      intro base i v j hv
      by_contra hnot
      apply hv
      exact exposedPrefix_column_support s a b base pins I p r (c i)
        (fun l _=>hr l) j.val (by simpa only [I,Set.mem_inter_iff,Set.mem_ofPred_eq] using hJ base j.val j.property) v (fun h=>hnot h.1))
    (fun base i=>indicatorVector_pairing (A base i) J (P base i (eta+g base)))
    hbad hesc (by intro i; simpa only [hPf, H, I, Exposure.quietEnergy, MeshPair.quietEnergy] using hloss i)
  have hPf' (base : T → Bool) (i : ℕ) : P base i (f base)=
      exposedSweep s a b base pins I p r (c i) (f base) := by
    simpa only [heq] using hPf base i
  simpa only [eta,indicatorVector_sq,Fintype.card_coe,heq,hPf',I] using h

end Heisenberg.Flow

end

noncomputable section
open scoped Classical Fin.NatCast
namespace Heisenberg.Schedule
variable {m Q : ℕ} [NeZero m]

def run (t : Fin m) (j : ℕ) : Fin m := t+(↑j:Fin m)

@[simp] lemma run_zero (t : Fin m) : run t 0=t := by simp [run]
lemma run_succ (t : Fin m) (j : ℕ) : run t (j+1)=finRotate m (run t j) := by
  simp [run,Nat.cast_add,add_assoc]
lemma run_val (t : Fin m) (j : ℕ) : (run t j).val=(t.val+j)%m := by
  simp [run,Fin.val_add,Nat.add_mod]
lemma run_inj (t : Fin m) {n : ℕ} (hn : n ≤ m) : Set.InjOn (run t) (Set.Iio n) := by
  intro i hi j hj h
  have he : (↑i:Fin m)=(↑j:Fin m) := add_left_cancel h
  have hh := congrArg Fin.val he
  simpa only [Fin.val_natCast,Nat.mod_eq_of_lt (lt_of_lt_of_le hi hn),
    Nat.mod_eq_of_lt (lt_of_lt_of_le hj hn)] using hh

def warm (t : Fin m) (Q : ℕ) : ℕ := Q-t.val%Q
def cut (t : Fin m) (Q : ℕ) (i : ℕ) : ℕ := warm t Q+i*Q

omit [NeZero m] in
lemma warm_pos (t : Fin m) (hQ : 0<Q) : 0<warm t Q := by
  have h := Nat.mod_lt t.val hQ
  unfold warm
  omega
omit [NeZero m] in
lemma warm_le (t : Fin m) : warm t Q≤Q := Nat.sub_le ..
omit [NeZero m] in
lemma cut_step (t : Fin m) (i : ℕ) : cut t Q (i+1)=cut t Q i+Q := by
  simp [cut,Nat.add_mul,Nat.add_assoc]
lemma cut_mod (t : Fin m) (hQ : 0<Q) (hdiv : Q∣m) (i j : ℕ) :
    (run t (cut t Q i+j)).val%Q=j%Q := by
  rw [run_val,Nat.mod_mod_of_dvd _ hdiv]
  have h := Nat.mod_lt t.val hQ
  have hw : (t.val+warm t Q)%Q=0 := by
    have he : t.val%Q+(Q-t.val%Q)=Q := Nat.add_sub_of_le h.le
    change (t.val+(Q-t.val%Q))%Q=0
    calc
      _ = (t.val%Q+(Q-t.val%Q))%Q := by simp [Nat.add_mod]
      _ = 0 := by rw [he,Nat.mod_self]
  have he : t.val+(cut t Q i+j)=(t.val+warm t Q)+i*Q+j := by simp [cut,Nat.add_assoc]
  rw [he]
  simp only [Nat.add_mod,hw,Nat.mul_mod_left,Nat.zero_mod,Nat.zero_add,Nat.mod_mod]

def round (t : Fin m) (Q j : ℕ) : ℕ := (t.val%Q+j)/Q
omit [NeZero m] in
lemma round_mono (t : Fin m) : Monotone (round t Q) := by
  intro i j hij
  exact Nat.div_le_div_right (Nat.add_le_add_left hij _)
omit [NeZero m] in
lemma round_lt (t : Fin m) (hQ : 0<Q) {j u : ℕ} (hj : j≤u*Q) : round t Q j<u+1 := by
  apply (Nat.div_lt_iff_lt_mul hQ).mpr
  have h := Nat.mod_lt t.val hQ
  nlinarith

def clock (t : Fin m) (Q g l : ℕ) : Fin m :=
  ⟨((t.val/Q+g)*Q+l)%m,Nat.mod_lt _ (NeZero.pos m)⟩
lemma clock_mod (t : Fin m) (hdiv : Q∣m) (g l : ℕ) :
    (clock t Q g l).val%Q=l%Q := by
  simp only [clock,Nat.mod_mod_of_dvd _ hdiv,Nat.add_mod,Nat.mul_mod_left,
    Nat.zero_add,Nat.mod_mod]
lemma clock_run (t : Fin m) (j : ℕ) :
    clock t Q (round t Q j) ((t.val+j)%Q)=run t j := by
  apply Fin.ext
  rw [run_val]
  change (((t.val/Q+(t.val%Q+j)/Q)*Q+(t.val+j)%Q)%m)=(t.val+j)%m
  congr 1
  have h₁ := Nat.mod_add_div t.val Q
  have h₂ := Nat.mod_add_div (t.val%Q+j) Q
  have h₃ : (t.val+j)%Q=(t.val%Q+j)%Q := by simp [Nat.add_mod]
  rw [h₃]
  nlinarith
lemma clock_run_phase (t : Fin m) (hdiv : Q∣m) (j : ℕ) :
    clock t Q (round t Q j) ((run t j).val%Q)=run t j := by
  rw [run_val,Nat.mod_mod_of_dvd _ hdiv]
  exact clock_run t j

end Heisenberg.Schedule
end
end

end OAI
