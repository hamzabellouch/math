import OAI.Combinatorics.SnakyCertificate.Cache
import OAI.Combinatorics.SnakyCertificate.TableList

namespace OAI

namespace SnakyCertificate.Check

theorem cache_height_block_0 : ∀ j : Fin 16, (cached (0 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_0 : ∀ i, 0 ≤ i → i < 16 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 0) (n := 16) cache_height_block_0

theorem cache_height_block_16 : ∀ j : Fin 16, (cached (16 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_16 : ∀ i, 16 ≤ i → i < 32 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 16) (n := 16) cache_height_block_16

theorem cache_height_block_32 : ∀ j : Fin 16, (cached (32 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_32 : ∀ i, 32 ≤ i → i < 48 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 32) (n := 16) cache_height_block_32

theorem cache_height_block_48 : ∀ j : Fin 16, (cached (48 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_48 : ∀ i, 48 ≤ i → i < 64 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 48) (n := 16) cache_height_block_48

theorem cache_height_block_64 : ∀ j : Fin 16, (cached (64 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_64 : ∀ i, 64 ≤ i → i < 80 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 64) (n := 16) cache_height_block_64

theorem cache_height_block_80 : ∀ j : Fin 16, (cached (80 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_80 : ∀ i, 80 ≤ i → i < 96 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 80) (n := 16) cache_height_block_80

theorem cache_height_block_96 : ∀ j : Fin 16, (cached (96 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_96 : ∀ i, 96 ≤ i → i < 112 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 96) (n := 16) cache_height_block_96

theorem cache_height_block_112 : ∀ j : Fin 16, (cached (112 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_112 : ∀ i, 112 ≤ i → i < 128 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 112) (n := 16) cache_height_block_112

theorem cache_height_block_128 : ∀ j : Fin 16, (cached (128 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_128 : ∀ i, 128 ≤ i → i < 144 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 128) (n := 16) cache_height_block_128

theorem cache_height_block_144 : ∀ j : Fin 16, (cached (144 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_144 : ∀ i, 144 ≤ i → i < 160 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 144) (n := 16) cache_height_block_144

theorem cache_height_block_160 : ∀ j : Fin 16, (cached (160 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_160 : ∀ i, 160 ≤ i → i < 176 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 160) (n := 16) cache_height_block_160

theorem cache_height_block_176 : ∀ j : Fin 16, (cached (176 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_176 : ∀ i, 176 ≤ i → i < 192 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 176) (n := 16) cache_height_block_176

theorem cache_height_block_192 : ∀ j : Fin 16, (cached (192 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_192 : ∀ i, 192 ≤ i → i < 208 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 192) (n := 16) cache_height_block_192

theorem cache_height_block_208 : ∀ j : Fin 16, (cached (208 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_208 : ∀ i, 208 ≤ i → i < 224 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 208) (n := 16) cache_height_block_208

theorem cache_height_block_224 : ∀ j : Fin 16, (cached (224 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_224 : ∀ i, 224 ≤ i → i < 240 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 224) (n := 16) cache_height_block_224

theorem cache_height_block_240 : ∀ j : Fin 16, (cached (240 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_240 : ∀ i, 240 ≤ i → i < 256 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 240) (n := 16) cache_height_block_240

theorem cache_height_block_256 : ∀ j : Fin 16, (cached (256 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_256 : ∀ i, 256 ≤ i → i < 272 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 256) (n := 16) cache_height_block_256

theorem cache_height_block_272 : ∀ j : Fin 16, (cached (272 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_272 : ∀ i, 272 ≤ i → i < 288 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 272) (n := 16) cache_height_block_272

theorem cache_height_block_288 : ∀ j : Fin 16, (cached (288 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_288 : ∀ i, 288 ≤ i → i < 304 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 288) (n := 16) cache_height_block_288

theorem cache_height_block_304 : ∀ j : Fin 16, (cached (304 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_304 : ∀ i, 304 ≤ i → i < 320 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 304) (n := 16) cache_height_block_304

theorem cache_height_block_320 : ∀ j : Fin 16, (cached (320 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_320 : ∀ i, 320 ≤ i → i < 336 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 320) (n := 16) cache_height_block_320

theorem cache_height_block_336 : ∀ j : Fin 16, (cached (336 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_336 : ∀ i, 336 ≤ i → i < 352 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 336) (n := 16) cache_height_block_336

theorem cache_height_block_352 : ∀ j : Fin 16, (cached (352 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_352 : ∀ i, 352 ≤ i → i < 368 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 352) (n := 16) cache_height_block_352

theorem cache_height_block_368 : ∀ j : Fin 16, (cached (368 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_368 : ∀ i, 368 ≤ i → i < 384 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 368) (n := 16) cache_height_block_368

theorem cache_height_block_384 : ∀ j : Fin 16, (cached (384 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_384 : ∀ i, 384 ≤ i → i < 400 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 384) (n := 16) cache_height_block_384

theorem cache_height_block_400 : ∀ j : Fin 16, (cached (400 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_400 : ∀ i, 400 ≤ i → i < 416 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 400) (n := 16) cache_height_block_400

theorem cache_height_block_416 : ∀ j : Fin 16, (cached (416 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_416 : ∀ i, 416 ≤ i → i < 432 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 416) (n := 16) cache_height_block_416

theorem cache_height_block_432 : ∀ j : Fin 16, (cached (432 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_432 : ∀ i, 432 ≤ i → i < 448 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 432) (n := 16) cache_height_block_432

theorem cache_height_block_448 : ∀ j : Fin 16, (cached (448 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_448 : ∀ i, 448 ≤ i → i < 464 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 448) (n := 16) cache_height_block_448

theorem cache_height_block_464 : ∀ j : Fin 16, (cached (464 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_464 : ∀ i, 464 ≤ i → i < 480 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 464) (n := 16) cache_height_block_464

theorem cache_height_block_480 : ∀ j : Fin 16, (cached (480 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_480 : ∀ i, 480 ≤ i → i < 496 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 480) (n := 16) cache_height_block_480

theorem cache_height_block_496 : ∀ j : Fin 16, (cached (496 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_496 : ∀ i, 496 ≤ i → i < 512 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 496) (n := 16) cache_height_block_496

theorem cache_height_block_512 : ∀ j : Fin 16, (cached (512 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_512 : ∀ i, 512 ≤ i → i < 528 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 512) (n := 16) cache_height_block_512

theorem cache_height_block_528 : ∀ j : Fin 16, (cached (528 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_528 : ∀ i, 528 ≤ i → i < 544 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 528) (n := 16) cache_height_block_528

theorem cache_height_block_544 : ∀ j : Fin 16, (cached (544 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_544 : ∀ i, 544 ≤ i → i < 560 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 544) (n := 16) cache_height_block_544

theorem cache_height_block_560 : ∀ j : Fin 16, (cached (560 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_560 : ∀ i, 560 ≤ i → i < 576 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 560) (n := 16) cache_height_block_560

theorem cache_height_block_576 : ∀ j : Fin 16, (cached (576 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_576 : ∀ i, 576 ≤ i → i < 592 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 576) (n := 16) cache_height_block_576

theorem cache_height_block_592 : ∀ j : Fin 16, (cached (592 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_592 : ∀ i, 592 ≤ i → i < 608 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 592) (n := 16) cache_height_block_592

theorem cache_height_block_608 : ∀ j : Fin 8, (cached (608 + j.val)).height ≤ 34 := by
  decide +kernel

theorem cache_height_range_608 : ∀ i, 608 ≤ i → i < 616 → (cached i).height ≤ 34 :=
  fin_block_range (P := fun i => (cached i).height ≤ 34) (a := 608) (n := 8) cache_height_block_608

theorem cache_height_range_0_32 : ∀ i, 0 ≤ i → i < 32 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_0 cache_height_range_16

theorem cache_height_range_32_64 : ∀ i, 32 ≤ i → i < 64 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_32 cache_height_range_48

theorem cache_height_range_0_64 : ∀ i, 0 ≤ i → i < 64 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_0_32 cache_height_range_32_64

theorem cache_height_range_64_96 : ∀ i, 64 ≤ i → i < 96 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_64 cache_height_range_80

theorem cache_height_range_112_144 : ∀ i, 112 ≤ i → i < 144 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_112 cache_height_range_128

theorem cache_height_range_96_144 : ∀ i, 96 ≤ i → i < 144 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_96 cache_height_range_112_144

theorem cache_height_range_64_144 : ∀ i, 64 ≤ i → i < 144 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_64_96 cache_height_range_96_144

theorem cache_height_range_0_144 : ∀ i, 0 ≤ i → i < 144 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_0_64 cache_height_range_64_144

theorem cache_height_range_144_176 : ∀ i, 144 ≤ i → i < 176 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_144 cache_height_range_160

theorem cache_height_range_192_224 : ∀ i, 192 ≤ i → i < 224 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_192 cache_height_range_208

theorem cache_height_range_176_224 : ∀ i, 176 ≤ i → i < 224 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_176 cache_height_range_192_224

theorem cache_height_range_144_224 : ∀ i, 144 ≤ i → i < 224 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_144_176 cache_height_range_176_224

theorem cache_height_range_224_256 : ∀ i, 224 ≤ i → i < 256 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_224 cache_height_range_240

theorem cache_height_range_272_304 : ∀ i, 272 ≤ i → i < 304 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_272 cache_height_range_288

theorem cache_height_range_256_304 : ∀ i, 256 ≤ i → i < 304 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_256 cache_height_range_272_304

theorem cache_height_range_224_304 : ∀ i, 224 ≤ i → i < 304 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_224_256 cache_height_range_256_304

theorem cache_height_range_144_304 : ∀ i, 144 ≤ i → i < 304 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_144_224 cache_height_range_224_304

theorem cache_height_range_0_304 : ∀ i, 0 ≤ i → i < 304 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_0_144 cache_height_range_144_304

theorem cache_height_range_304_336 : ∀ i, 304 ≤ i → i < 336 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_304 cache_height_range_320

theorem cache_height_range_352_384 : ∀ i, 352 ≤ i → i < 384 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_352 cache_height_range_368

theorem cache_height_range_336_384 : ∀ i, 336 ≤ i → i < 384 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_336 cache_height_range_352_384

theorem cache_height_range_304_384 : ∀ i, 304 ≤ i → i < 384 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_304_336 cache_height_range_336_384

theorem cache_height_range_384_416 : ∀ i, 384 ≤ i → i < 416 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_384 cache_height_range_400

theorem cache_height_range_432_464 : ∀ i, 432 ≤ i → i < 464 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_432 cache_height_range_448

theorem cache_height_range_416_464 : ∀ i, 416 ≤ i → i < 464 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_416 cache_height_range_432_464

theorem cache_height_range_384_464 : ∀ i, 384 ≤ i → i < 464 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_384_416 cache_height_range_416_464

theorem cache_height_range_304_464 : ∀ i, 304 ≤ i → i < 464 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_304_384 cache_height_range_384_464

theorem cache_height_range_464_496 : ∀ i, 464 ≤ i → i < 496 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_464 cache_height_range_480

theorem cache_height_range_512_544 : ∀ i, 512 ≤ i → i < 544 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_512 cache_height_range_528

theorem cache_height_range_496_544 : ∀ i, 496 ≤ i → i < 544 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_496 cache_height_range_512_544

theorem cache_height_range_464_544 : ∀ i, 464 ≤ i → i < 544 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_464_496 cache_height_range_496_544

theorem cache_height_range_544_576 : ∀ i, 544 ≤ i → i < 576 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_544 cache_height_range_560

theorem cache_height_range_592_616 : ∀ i, 592 ≤ i → i < 616 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_592 cache_height_range_608

theorem cache_height_range_576_616 : ∀ i, 576 ≤ i → i < 616 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_576 cache_height_range_592_616

theorem cache_height_range_544_616 : ∀ i, 544 ≤ i → i < 616 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_544_576 cache_height_range_576_616

theorem cache_height_range_464_616 : ∀ i, 464 ≤ i → i < 616 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_464_544 cache_height_range_544_616

theorem cache_height_range_304_616 : ∀ i, 304 ≤ i → i < 616 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_304_464 cache_height_range_464_616

theorem cache_height_range_0_616 : ∀ i, 0 ≤ i → i < 616 → (fun i => (cached i).height ≤ 34) i :=
  merge_ranges cache_height_range_0_304 cache_height_range_304_616

theorem cache_heights (i : ℕ) (hi : i < 616) : (cached i).height ≤ 34 :=
  cache_height_range_0_616 i (Nat.zero_le _) hi

end SnakyCertificate.Check

end OAI
