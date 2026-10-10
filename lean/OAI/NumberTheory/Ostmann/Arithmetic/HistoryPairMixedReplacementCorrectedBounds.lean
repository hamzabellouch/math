import OAI.NumberTheory.Ostmann.Arithmetic.HistoryActiveSourceDomain

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryActiveCoordinates
open PrimeCellFreezing
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def keyLogEndpoint (I : Finset κ) (background : κ → ℝ) (endpoint : I → ℝ) (keys : List κ) : ℝ :=
  (keys.map (logInsert I background endpoint)).sum

omit [Fintype κ] in
theorem log_keyProduct_insert_exp [Fintype κ] (I : Finset κ) (background : κ → ℝ)
    (hbackground : ∀i,0 < background i) (z : I → ℝ) (keys : List κ) :
    Real.log ((keys.map (insert I background (fun i => Real.exp (z i)))).prod) =
      keyLogEndpoint I background z keys := by
  rw [insert_exp I background z hbackground]
  rw [Real.log_list_prod (by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    exact (Real.exp_pos _).ne')]
  simp only [List.map_map,Function.comp_def,Real.log_exp,keyLogEndpoint]

omit [Fintype κ] in
private theorem keyLogEndpoint_mono (I : Finset κ) (background : κ → ℝ)
    (a b : I → ℝ) (hab : ∀i,a i ≤ b i) (keys : List κ) :
    keyLogEndpoint I background a keys ≤ keyLogEndpoint I background b keys := by
  induction keys with
  | nil => exact le_rfl
  | cons i keys ih =>
    change logInsert I background a i + keyLogEndpoint I background a keys ≤
      logInsert I background b i + keyLogEndpoint I background b keys
    apply add_le_add _ ih
    unfold logInsert
    split_ifs with hi
    · exact hab ⟨i,hi⟩
    · exact le_rfl

theorem keyProduct_log_bounds (I : Finset κ) (background : κ → ℝ)
    (hbackground : ∀i,0 < background i) (lo hi z : I → ℝ)
    (hz : z ∈ logRectangle lo hi) (keys : List κ) :
    keyLogEndpoint I background lo keys ≤
      Real.log ((keys.map (insert I background (fun i => Real.exp (z i)))).prod) ∧
    Real.log ((keys.map (insert I background (fun i => Real.exp (z i)))).prod) ≤
      keyLogEndpoint I background hi keys := by
  rw [log_keyProduct_insert_exp I background hbackground z keys]
  exact ⟨keyLogEndpoint_mono I background lo z (fun i => (hz i (Set.mem_univ _)).1) keys,
    keyLogEndpoint_mono I background z hi (fun i => (hz i (Set.mem_univ _)).2) keys⟩

structure CounterpartBounds (T U WH Wu : ℝ) (Hkeys Ukeys : List κ)
    (I : Finset κ) (background : κ → ℝ) (lo hi : I → ℝ) : Prop where
  lower : T-WH ≤ keyLogEndpoint I background lo Hkeys
  upper : keyLogEndpoint I background hi Ukeys ≤ U+Wu

omit [Fintype κ] in

theorem counterpartBounds_endpoints (T U : ℝ) (Hkeys Ukeys : List κ)
    (I : Finset κ) (background : κ → ℝ) (lo hi : I → ℝ) :
    CounterpartBounds T U (T-keyLogEndpoint I background lo Hkeys)
      (keyLogEndpoint I background hi Ukeys-U) Hkeys Ukeys I background lo hi := by
  constructor <;> linarith

theorem CounterpartBounds.log_products {T U WH Wu : ℝ} {Hkeys Ukeys : List κ}
    {I : Finset κ} {background : κ → ℝ} {lo hi : I → ℝ}
    (hh : CounterpartBounds T U WH Wu Hkeys Ukeys I background lo hi)
    (hbackground : ∀i,0 < background i) (z : I → ℝ) (hz : z ∈ logRectangle lo hi) :
    T-WH ≤ Real.log ((Hkeys.map (insert I background (fun i => Real.exp (z i)))).prod) ∧
    Real.log ((Ukeys.map (insert I background (fun i => Real.exp (z i)))).prod) ≤ U+Wu :=
  ⟨hh.lower.trans (keyProduct_log_bounds I background hbackground lo hi z hz Hkeys).1,
    (keyProduct_log_bounds I background hbackground lo hi z hz Ukeys).2.trans hh.upper⟩

end Ostmann.Arithmetic.HistoryActiveCoordinates

end

end OAI
